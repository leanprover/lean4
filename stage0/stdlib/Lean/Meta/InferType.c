// Lean compiler output
// Module: Lean.Meta.InferType
// Imports: public import Lean.Data.LBool public import Lean.Meta.Basic import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_ProjReductionKind_ctorIdx(uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2_value;
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.InferType.0.Lean.Expr.instantiateBetaRevRange.visit"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.InferType"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2_value;
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateApp!Impl"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__0;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Expr.instantiateBetaRevRange"};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__2_value;
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 42, .m_data = "assertion violation: stop ≤ args.size\n    "};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__3_value;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwFunctionExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "function expected"};
static const lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwFunctionExpected___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "incorrect number of universe levels "};
static const lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid projection"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nfrom type"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwTypeExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "type expected"};
static const lean_object* l_Lean_Meta_throwTypeExpected___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwTypeExpected___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwTypeExpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwTypeExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwUnknownMVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unknown metavariable '\?"};
static const lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwUnknownMVar___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__1;
static const lean_string_object l_Lean_Meta_throwUnknownMVar___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_throwUnknownMVar___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11_value;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withInferTypeConfig___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withInferTypeConfig___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected bound variable "};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "outParam"};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_isPropFormerType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_isPropFormerType___closed__0 = (const lean_object*)&l_Lean_Meta_isPropFormerType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected dependent type "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_arrowDomainsN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "type "};
static const lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_arrowDomainsN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_arrowDomainsN___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " does not have "};
static const lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_arrowDomainsN___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_arrowDomainsN___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_arrowDomainsN___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(lean_object* v_start_1_, lean_object* v_stop_2_, lean_object* v_args_3_, lean_object* v_vidx_4_, lean_object* v_offset_5_){
_start:
{
lean_object* v_n_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v_n_6_ = lean_nat_sub(v_stop_2_, v_start_1_);
v___x_7_ = lean_nat_add(v_offset_5_, v_n_6_);
v___x_8_ = lean_nat_dec_lt(v_vidx_4_, v___x_7_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_nat_sub(v_vidx_4_, v_n_6_);
lean_dec(v_n_6_);
v___x_10_ = l_Lean_Expr_bvar___override(v___x_9_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_n_6_);
v___x_11_ = l_Lean_instInhabitedExpr;
v___x_12_ = lean_nat_sub(v_vidx_4_, v_offset_5_);
v___x_13_ = lean_nat_sub(v_stop_2_, v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_sub(v___x_13_, v___x_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_array_get_borrowed(v___x_11_, v_args_3_, v___x_15_);
lean_dec(v___x_15_);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_expr_lift_loose_bvars(v___x_16_, v___x_17_, v_offset_5_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar___boxed(lean_object* v_start_19_, lean_object* v_stop_20_, lean_object* v_args_21_, lean_object* v_vidx_22_, lean_object* v_offset_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_19_, v_stop_20_, v_args_21_, v_vidx_22_, v_offset_23_);
lean_dec(v_offset_23_);
lean_dec(v_vidx_22_);
lean_dec_ref(v_args_21_);
lean_dec(v_stop_20_);
lean_dec(v_start_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
return v_x_25_;
}
else
{
lean_object* v_key_27_; lean_object* v_value_28_; lean_object* v_tail_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_56_; 
v_key_27_ = lean_ctor_get(v_x_26_, 0);
v_value_28_ = lean_ctor_get(v_x_26_, 1);
v_tail_29_ = lean_ctor_get(v_x_26_, 2);
v_isSharedCheck_56_ = !lean_is_exclusive(v_x_26_);
if (v_isSharedCheck_56_ == 0)
{
v___x_31_ = v_x_26_;
v_isShared_32_ = v_isSharedCheck_56_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_tail_29_);
lean_inc(v_value_28_);
lean_inc(v_key_27_);
lean_dec(v_x_26_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_56_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; uint64_t v_fold_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; size_t v___x_45_; size_t v___x_46_; size_t v___x_47_; size_t v___x_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v_fst_33_ = lean_ctor_get(v_key_27_, 0);
v_snd_34_ = lean_ctor_get(v_key_27_, 1);
v___x_35_ = lean_array_get_size(v_x_25_);
v___x_36_ = l_Lean_ExprStructEq_hash(v_fst_33_);
v___x_37_ = lean_uint64_of_nat(v_snd_34_);
v___x_38_ = lean_uint64_mix_hash(v___x_36_, v___x_37_);
v___x_39_ = 32ULL;
v___x_40_ = lean_uint64_shift_right(v___x_38_, v___x_39_);
v_fold_41_ = lean_uint64_xor(v___x_38_, v___x_40_);
v___x_42_ = 16ULL;
v___x_43_ = lean_uint64_shift_right(v_fold_41_, v___x_42_);
v___x_44_ = lean_uint64_xor(v_fold_41_, v___x_43_);
v___x_45_ = lean_uint64_to_usize(v___x_44_);
v___x_46_ = lean_usize_of_nat(v___x_35_);
v___x_47_ = ((size_t)1ULL);
v___x_48_ = lean_usize_sub(v___x_46_, v___x_47_);
v___x_49_ = lean_usize_land(v___x_45_, v___x_48_);
v___x_50_ = lean_array_uget_borrowed(v_x_25_, v___x_49_);
lean_inc(v___x_50_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 2, v___x_50_);
v___x_52_ = v___x_31_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_key_27_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_value_28_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v___x_50_);
v___x_52_ = v_reuseFailAlloc_55_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; 
v___x_53_ = lean_array_uset(v_x_25_, v___x_49_, v___x_52_);
v_x_25_ = v___x_53_;
v_x_26_ = v_tail_29_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(lean_object* v_i_57_, lean_object* v_source_58_, lean_object* v_target_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_source_58_);
v___x_61_ = lean_nat_dec_lt(v_i_57_, v___x_60_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_source_58_);
lean_dec(v_i_57_);
return v_target_59_;
}
else
{
lean_object* v_es_62_; lean_object* v___x_63_; lean_object* v_source_64_; lean_object* v_target_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_es_62_ = lean_array_fget(v_source_58_, v_i_57_);
v___x_63_ = lean_box(0);
v_source_64_ = lean_array_fset(v_source_58_, v_i_57_, v___x_63_);
v_target_65_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_target_59_, v_es_62_);
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_i_57_, v___x_66_);
lean_dec(v_i_57_);
v_i_57_ = v___x_67_;
v_source_58_ = v_source_64_;
v_target_59_ = v_target_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(lean_object* v_data_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_nbuckets_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_array_get_size(v_data_69_);
v___x_71_ = lean_unsigned_to_nat(2u);
v_nbuckets_72_ = lean_nat_mul(v___x_70_, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_box(0);
v___x_75_ = lean_mk_array(v_nbuckets_72_, v___x_74_);
v___x_76_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v___x_73_, v_data_69_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object* v_a_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
else
{
lean_object* v_key_80_; lean_object* v_tail_81_; uint8_t v___y_83_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; uint8_t v___x_89_; 
v_key_80_ = lean_ctor_get(v_x_78_, 0);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v_fst_85_ = lean_ctor_get(v_key_80_, 0);
v_snd_86_ = lean_ctor_get(v_key_80_, 1);
v_fst_87_ = lean_ctor_get(v_a_77_, 0);
v_snd_88_ = lean_ctor_get(v_a_77_, 1);
v___x_89_ = l_Lean_ExprStructEq_beq(v_fst_85_, v_fst_87_);
if (v___x_89_ == 0)
{
v___y_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_eq(v_snd_86_, v_snd_88_);
v___y_83_ = v___x_90_;
goto v___jp_82_;
}
v___jp_82_:
{
if (v___y_83_ == 0)
{
v_x_78_ = v_tail_81_;
goto _start;
}
else
{
return v___y_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object* v_a_91_, lean_object* v_x_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_91_, v_x_92_);
lean_dec(v_x_92_);
lean_dec_ref(v_a_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(lean_object* v_a_95_, lean_object* v_b_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
lean_dec(v_b_96_);
lean_dec_ref(v_a_95_);
return v_x_97_;
}
else
{
lean_object* v_key_98_; lean_object* v_value_99_; lean_object* v_tail_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_119_; 
v_key_98_ = lean_ctor_get(v_x_97_, 0);
v_value_99_ = lean_ctor_get(v_x_97_, 1);
v_tail_100_ = lean_ctor_get(v_x_97_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_119_ == 0)
{
v___x_102_ = v_x_97_;
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_tail_100_);
lean_inc(v_value_99_);
lean_inc(v_key_98_);
lean_dec(v_x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
uint8_t v___y_105_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; uint8_t v___x_117_; 
v_fst_113_ = lean_ctor_get(v_key_98_, 0);
v_snd_114_ = lean_ctor_get(v_key_98_, 1);
v_fst_115_ = lean_ctor_get(v_a_95_, 0);
v_snd_116_ = lean_ctor_get(v_a_95_, 1);
v___x_117_ = l_Lean_ExprStructEq_beq(v_fst_113_, v_fst_115_);
if (v___x_117_ == 0)
{
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_eq(v_snd_114_, v_snd_116_);
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_95_, v_b_96_, v_tail_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_106_);
v___x_108_ = v___x_102_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_key_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_value_99_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v___x_111_; 
lean_dec(v_value_99_);
lean_dec(v_key_98_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_b_96_);
lean_ctor_set(v___x_102_, 0, v_a_95_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_95_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_b_96_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_tail_100_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object* v_m_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
lean_object* v_size_123_; lean_object* v_buckets_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_171_; 
v_size_123_ = lean_ctor_get(v_m_120_, 0);
v_buckets_124_ = lean_ctor_get(v_m_120_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_m_120_);
if (v_isSharedCheck_171_ == 0)
{
v___x_126_ = v_m_120_;
v_isShared_127_ = v_isSharedCheck_171_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_buckets_124_);
lean_inc(v_size_123_);
lean_dec(v_m_120_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_171_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v_fold_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v_bkt_145_; uint8_t v___x_146_; 
v_fst_128_ = lean_ctor_get(v_a_121_, 0);
v_snd_129_ = lean_ctor_get(v_a_121_, 1);
v___x_130_ = lean_array_get_size(v_buckets_124_);
v___x_131_ = l_Lean_ExprStructEq_hash(v_fst_128_);
v___x_132_ = lean_uint64_of_nat(v_snd_129_);
v___x_133_ = lean_uint64_mix_hash(v___x_131_, v___x_132_);
v___x_134_ = 32ULL;
v___x_135_ = lean_uint64_shift_right(v___x_133_, v___x_134_);
v_fold_136_ = lean_uint64_xor(v___x_133_, v___x_135_);
v___x_137_ = 16ULL;
v___x_138_ = lean_uint64_shift_right(v_fold_136_, v___x_137_);
v___x_139_ = lean_uint64_xor(v_fold_136_, v___x_138_);
v___x_140_ = lean_uint64_to_usize(v___x_139_);
v___x_141_ = lean_usize_of_nat(v___x_130_);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_sub(v___x_141_, v___x_142_);
v___x_144_ = lean_usize_land(v___x_140_, v___x_143_);
v_bkt_145_ = lean_array_uget_borrowed(v_buckets_124_, v___x_144_);
v___x_146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_121_, v_bkt_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v_size_x27_148_; lean_object* v___x_149_; lean_object* v_buckets_x27_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v_size_x27_148_ = lean_nat_add(v_size_123_, v___x_147_);
lean_dec(v_size_123_);
lean_inc(v_bkt_145_);
v___x_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_149_, 0, v_a_121_);
lean_ctor_set(v___x_149_, 1, v_b_122_);
lean_ctor_set(v___x_149_, 2, v_bkt_145_);
v_buckets_x27_150_ = lean_array_uset(v_buckets_124_, v___x_144_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lean_nat_mul(v_size_x27_148_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(3u);
v___x_154_ = lean_nat_div(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_array_get_size(v_buckets_x27_150_);
v___x_156_ = lean_nat_dec_le(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v_val_157_; lean_object* v___x_159_; 
v_val_157_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_buckets_x27_150_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_val_157_);
lean_ctor_set(v___x_126_, 0, v_size_x27_148_);
v___x_159_ = v___x_126_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_148_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_val_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_162_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_buckets_x27_150_);
lean_ctor_set(v___x_126_, 0, v_size_x27_148_);
v___x_162_ = v___x_126_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_148_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_buckets_x27_150_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v___x_164_; lean_object* v_buckets_x27_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
lean_inc(v_bkt_145_);
v___x_164_ = lean_box(0);
v_buckets_x27_165_ = lean_array_uset(v_buckets_124_, v___x_144_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_121_, v_b_122_, v_bkt_145_);
v___x_167_ = lean_array_uset(v_buckets_x27_165_, v___x_144_, v___x_166_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_167_);
v___x_169_ = v___x_126_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(lean_object* v_msg_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_Lean_instInhabitedExpr;
v___x_174_ = lean_panic_fn_borrowed(v___x_173_, v_msg_172_);
return v___x_174_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___f_177_; 
v___x_176_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_177_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_177_, 0, v___x_176_);
return v___f_177_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_4808__overap_208_; lean_object* v___x_209_; 
v___x_189_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_190_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1);
v___f_191_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_191_, 0, v___x_189_);
lean_closure_set(v___f_191_, 1, v___f_190_);
v___x_192_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_193_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_194_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_194_, 0, v___x_192_);
lean_closure_set(v___f_194_, 1, v___f_193_);
v___f_195_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_196_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___f_198_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7));
v___f_199_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8));
v___f_200_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9));
v___f_201_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10));
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___f_195_);
lean_ctor_set(v___x_202_, 1, v___f_196_);
v___x_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___f_197_);
lean_ctor_set(v___x_203_, 2, v___f_198_);
lean_ctor_set(v___x_203_, 3, v___f_199_);
lean_ctor_set(v___x_203_, 4, v___f_200_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___f_201_);
v___x_205_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_191_, v___f_194_, v___x_204_);
v___x_206_ = l_Lean_instInhabitedExpr;
v___x_207_ = l_instInhabitedOfMonad___redArg(v___x_205_, v___x_206_);
v___x_4808__overap_208_ = lean_panic_fn_borrowed(v___x_207_, v_msg_187_);
lean_dec(v___x_207_);
v___x_209_ = lean_apply_1(v___x_4808__overap_208_, v___y_188_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object* v_a_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v_key_213_; lean_object* v_value_214_; lean_object* v_tail_215_; uint8_t v___y_217_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; uint8_t v___x_224_; 
v_key_213_ = lean_ctor_get(v_x_211_, 0);
v_value_214_ = lean_ctor_get(v_x_211_, 1);
v_tail_215_ = lean_ctor_get(v_x_211_, 2);
v_fst_220_ = lean_ctor_get(v_key_213_, 0);
v_snd_221_ = lean_ctor_get(v_key_213_, 1);
v_fst_222_ = lean_ctor_get(v_a_210_, 0);
v_snd_223_ = lean_ctor_get(v_a_210_, 1);
v___x_224_ = l_Lean_ExprStructEq_beq(v_fst_220_, v_fst_222_);
if (v___x_224_ == 0)
{
v___y_217_ = v___x_224_;
goto v___jp_216_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_eq(v_snd_221_, v_snd_223_);
v___y_217_ = v___x_225_;
goto v___jp_216_;
}
v___jp_216_:
{
if (v___y_217_ == 0)
{
v_x_211_ = v_tail_215_;
goto _start;
}
else
{
lean_object* v___x_219_; 
lean_inc(v_value_214_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_value_214_);
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object* v_a_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_226_, v_x_227_);
lean_dec(v_x_227_);
lean_dec_ref(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object* v_m_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_buckets_231_; lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_buckets_231_ = lean_ctor_get(v_m_229_, 1);
v_fst_232_ = lean_ctor_get(v_a_230_, 0);
v_snd_233_ = lean_ctor_get(v_a_230_, 1);
v___x_234_ = lean_array_get_size(v_buckets_231_);
v___x_235_ = l_Lean_ExprStructEq_hash(v_fst_232_);
v___x_236_ = lean_uint64_of_nat(v_snd_233_);
v___x_237_ = lean_uint64_mix_hash(v___x_235_, v___x_236_);
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___x_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___x_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_234_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_buckets_231_, v___x_248_);
v___x_250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_230_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object* v_m_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_251_, v_a_252_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_m_251_);
return v_res_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_258_ = lean_unsigned_to_nat(21u);
v___x_259_ = lean_unsigned_to_nat(96u);
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_262_ = l_mkPanicMessageWithDecl(v___x_261_, v___x_260_, v___x_259_, v___x_258_, v___x_257_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_264_ = lean_unsigned_to_nat(21u);
v___x_265_ = lean_unsigned_to_nat(97u);
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_268_ = l_mkPanicMessageWithDecl(v___x_267_, v___x_266_, v___x_265_, v___x_264_, v___x_263_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_270_ = lean_unsigned_to_nat(21u);
v___x_271_ = lean_unsigned_to_nat(98u);
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_274_ = l_mkPanicMessageWithDecl(v___x_273_, v___x_272_, v___x_271_, v___x_270_, v___x_269_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_276_ = lean_unsigned_to_nat(21u);
v___x_277_ = lean_unsigned_to_nat(95u);
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_280_ = l_mkPanicMessageWithDecl(v___x_279_, v___x_278_, v___x_277_, v___x_276_, v___x_275_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object* v_start_281_, lean_object* v_stop_282_, lean_object* v_args_283_, lean_object* v_e_284_, lean_object* v_offset_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = l_Lean_Expr_looseBVarRange(v_e_284_);
v___x_288_ = lean_nat_dec_le(v___x_287_, v_offset_285_);
lean_dec(v___x_287_);
if (v___x_288_ == 0)
{
if (lean_obj_tag(v_e_284_) == 5)
{
lean_object* v_fn_289_; lean_object* v_arg_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_fn_289_ = lean_ctor_get(v_e_284_, 0);
lean_inc_ref(v_fn_289_);
v_arg_290_ = lean_ctor_get(v_e_284_, 1);
lean_inc_ref(v_arg_290_);
lean_inc(v_offset_285_);
lean_inc_ref(v_e_284_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_e_284_);
lean_ctor_set(v___x_291_, 1, v_offset_285_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_286_, v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_293_; lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v___x_293_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_281_, v_stop_282_, v_args_283_, v_e_284_, v_fn_289_, v_arg_290_, v_offset_285_, v_a_286_);
v_fst_294_ = lean_ctor_get(v___x_293_, 0);
v_snd_295_ = lean_ctor_get(v___x_293_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snd_295_);
lean_inc(v_fst_294_);
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_inc(v_fst_294_);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_295_, v___x_291_, v_fst_294_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_fst_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_val_304_; lean_object* v___x_305_; 
lean_dec_ref_known(v___x_291_, 2);
lean_dec_ref(v_arg_290_);
lean_dec_ref_known(v_e_284_, 2);
lean_dec_ref(v_fn_289_);
lean_dec(v_offset_285_);
v_val_304_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v___x_292_, 1);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_val_304_);
lean_ctor_set(v___x_305_, 1, v_a_286_);
return v___x_305_;
}
}
else
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_281_, v_stop_282_, v_args_283_, v_e_284_, v_offset_285_, v_a_286_);
return v___x_306_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_offset_285_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_e_284_);
lean_ctor_set(v___x_307_, 1, v_a_286_);
return v___x_307_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2));
v___x_312_ = lean_unsigned_to_nat(18u);
v___x_313_ = lean_unsigned_to_nat(1847u);
v___x_314_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_316_ = l_mkPanicMessageWithDecl(v___x_315_, v___x_314_, v___x_313_, v___x_312_, v___x_311_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_317_, lean_object* v_stop_318_, lean_object* v_args_319_, lean_object* v_e_320_, lean_object* v_f_321_, lean_object* v_a_322_, lean_object* v_offset_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_328_; 
lean_inc(v_offset_323_);
v___x_325_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_317_, v_stop_318_, v_args_319_, v_f_321_, v_offset_323_, v_a_324_);
v_fst_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_fst_326_);
v_snd_327_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_snd_327_);
lean_dec_ref(v___x_325_);
v___x_328_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_317_, v_stop_318_, v_args_319_, v_a_322_, v_offset_323_, v_snd_327_);
if (lean_obj_tag(v_e_320_) == 5)
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_353_; 
v_fst_329_ = lean_ctor_get(v___x_328_, 0);
v_snd_330_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_353_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_snd_330_);
lean_inc(v_fst_329_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fn_334_; lean_object* v_arg_335_; size_t v___x_336_; size_t v___x_337_; uint8_t v___x_338_; 
v_fn_334_ = lean_ctor_get(v_e_320_, 0);
v_arg_335_ = lean_ctor_get(v_e_320_, 1);
v___x_336_ = lean_ptr_addr(v_fn_334_);
v___x_337_ = lean_ptr_addr(v_fst_326_);
v___x_338_ = lean_usize_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec_ref_known(v_e_320_, 2);
v___x_339_ = l_Lean_Expr_app___override(v_fst_326_, v_fst_329_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_339_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_snd_330_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
size_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_ptr_addr(v_arg_335_);
v___x_344_ = lean_ptr_addr(v_fst_329_);
v___x_345_ = lean_usize_dec_eq(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec_ref_known(v_e_320_, 2);
v___x_346_ = l_Lean_Expr_app___override(v_fst_326_, v_fst_329_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_346_);
v___x_348_ = v___x_332_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_snd_330_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
else
{
lean_object* v___x_351_; 
lean_dec(v_fst_329_);
lean_dec(v_fst_326_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v_e_320_);
v___x_351_ = v___x_332_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_e_320_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_snd_330_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_snd_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_fst_326_);
lean_dec_ref(v_e_320_);
v_snd_354_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v___x_328_, 0);
lean_dec(v_unused_364_);
v___x_356_ = v___x_328_;
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snd_354_);
lean_dec(v___x_328_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_358_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_359_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_358_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_359_);
v___x_361_ = v___x_356_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_snd_354_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_366_ = lean_unsigned_to_nat(21u);
v___x_367_ = lean_unsigned_to_nat(99u);
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_370_ = l_mkPanicMessageWithDecl(v___x_369_, v___x_368_, v___x_367_, v___x_366_, v___x_365_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_371_, lean_object* v_stop_372_, lean_object* v_args_373_, lean_object* v_e_374_, lean_object* v_offset_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = l_Lean_Expr_looseBVarRange(v_e_374_);
v___x_378_ = lean_nat_dec_le(v___x_377_, v_offset_375_);
lean_dec(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___y_386_; lean_object* v___x_389_; 
lean_inc(v_offset_375_);
lean_inc_ref(v_e_374_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_e_374_);
lean_ctor_set(v___x_379_, 1, v_offset_375_);
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_376_, v___x_379_);
if (lean_obj_tag(v___x_389_) == 0)
{
switch(lean_obj_tag(v_e_374_))
{
case 0:
{
lean_object* v_deBruijnIndex_390_; lean_object* v___x_391_; 
v_deBruijnIndex_390_ = lean_ctor_get(v_e_374_, 0);
lean_inc(v_deBruijnIndex_390_);
lean_dec_ref_known(v_e_374_, 1);
v___x_391_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_371_, v_stop_372_, v_args_373_, v_deBruijnIndex_390_, v_offset_375_);
lean_dec(v_offset_375_);
lean_dec(v_deBruijnIndex_390_);
v_fst_381_ = v___x_391_;
v_snd_382_ = v_a_376_;
goto v___jp_380_;
}
case 1:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref_known(v_e_374_, 1);
lean_dec(v_offset_375_);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_393_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_392_, v_a_376_);
v___y_386_ = v___x_393_;
goto v___jp_385_;
}
case 2:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref_known(v_e_374_, 1);
lean_dec(v_offset_375_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_395_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_394_, v_a_376_);
v___y_386_ = v___x_395_;
goto v___jp_385_;
}
case 3:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref_known(v_e_374_, 1);
lean_dec(v_offset_375_);
v___x_396_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_397_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_396_, v_a_376_);
v___y_386_ = v___x_397_;
goto v___jp_385_;
}
case 4:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref_known(v_e_374_, 2);
lean_dec(v_offset_375_);
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_399_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_398_, v_a_376_);
v___y_386_ = v___x_399_;
goto v___jp_385_;
}
case 5:
{
lean_object* v_fn_400_; lean_object* v_arg_401_; lean_object* v_head_402_; uint8_t v___x_403_; 
v_fn_400_ = lean_ctor_get(v_e_374_, 0);
v_arg_401_ = lean_ctor_get(v_e_374_, 1);
v_head_402_ = l_Lean_Expr_getAppFn(v_e_374_);
v___x_403_ = l_Lean_Expr_isBVar(v_head_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
lean_inc_ref(v_arg_401_);
lean_inc_ref(v_fn_400_);
lean_dec_ref(v_head_402_);
v___x_404_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_371_, v_stop_372_, v_args_373_, v_e_374_, v_fn_400_, v_arg_401_, v_offset_375_, v_a_376_);
v___y_386_ = v___x_404_;
goto v___jp_385_;
}
else
{
lean_object* v___x_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; size_t v_sz_411_; size_t v___x_412_; lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; 
lean_inc(v_offset_375_);
v___x_405_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_head_402_, v_offset_375_, v_a_376_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
v_snd_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v___x_405_);
v___x_408_ = l_Lean_Expr_getAppNumArgs(v_e_374_);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
lean_dec(v___x_408_);
v___x_410_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_374_, v___x_409_);
v_sz_411_ = lean_array_size(v___x_410_);
v___x_412_ = ((size_t)0ULL);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_371_, v_stop_372_, v_args_373_, v_offset_375_, v_sz_411_, v___x_412_, v___x_410_, v_snd_407_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_snd_415_);
lean_dec_ref(v___x_413_);
v___x_416_ = l_Lean_Expr_betaRev(v_fst_406_, v_fst_414_, v___x_378_, v___x_378_);
lean_dec(v_fst_414_);
v_fst_381_ = v___x_416_;
v_snd_382_ = v_snd_415_;
goto v___jp_380_;
}
}
case 6:
{
lean_object* v_binderName_417_; lean_object* v_binderType_418_; lean_object* v_body_419_; uint8_t v_binderInfo_420_; lean_object* v___x_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; size_t v___x_429_; size_t v___x_430_; uint8_t v___x_431_; 
v_binderName_417_ = lean_ctor_get(v_e_374_, 0);
v_binderType_418_ = lean_ctor_get(v_e_374_, 1);
v_body_419_ = lean_ctor_get(v_e_374_, 2);
v_binderInfo_420_ = lean_ctor_get_uint8(v_e_374_, sizeof(void*)*3 + 8);
lean_inc(v_offset_375_);
lean_inc_ref(v_binderType_418_);
v___x_421_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_binderType_418_, v_offset_375_, v_a_376_);
v_fst_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_fst_422_);
v_snd_423_ = lean_ctor_get(v___x_421_, 1);
lean_inc(v_snd_423_);
lean_dec_ref(v___x_421_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_offset_375_, v___x_424_);
lean_dec(v_offset_375_);
lean_inc_ref(v_body_419_);
v___x_426_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_body_419_, v___x_425_, v_snd_423_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v___x_429_ = lean_ptr_addr(v_binderType_418_);
v___x_430_ = lean_ptr_addr(v_fst_422_);
v___x_431_ = lean_usize_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v_binderName_417_);
lean_dec_ref_known(v_e_374_, 3);
v___x_432_ = l_Lean_Expr_lam___override(v_binderName_417_, v_fst_422_, v_fst_427_, v_binderInfo_420_);
v_fst_381_ = v___x_432_;
v_snd_382_ = v_snd_428_;
goto v___jp_380_;
}
else
{
size_t v___x_433_; size_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_ptr_addr(v_body_419_);
v___x_434_ = lean_ptr_addr(v_fst_427_);
v___x_435_ = lean_usize_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_inc(v_binderName_417_);
lean_dec_ref_known(v_e_374_, 3);
v___x_436_ = l_Lean_Expr_lam___override(v_binderName_417_, v_fst_422_, v_fst_427_, v_binderInfo_420_);
v_fst_381_ = v___x_436_;
v_snd_382_ = v_snd_428_;
goto v___jp_380_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_420_, v_binderInfo_420_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_inc(v_binderName_417_);
lean_dec_ref_known(v_e_374_, 3);
v___x_438_ = l_Lean_Expr_lam___override(v_binderName_417_, v_fst_422_, v_fst_427_, v_binderInfo_420_);
v_fst_381_ = v___x_438_;
v_snd_382_ = v_snd_428_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_427_);
lean_dec(v_fst_422_);
v_fst_381_ = v_e_374_;
v_snd_382_ = v_snd_428_;
goto v___jp_380_;
}
}
}
}
case 7:
{
lean_object* v_binderName_439_; lean_object* v_binderType_440_; lean_object* v_body_441_; uint8_t v_binderInfo_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v_binderName_439_ = lean_ctor_get(v_e_374_, 0);
v_binderType_440_ = lean_ctor_get(v_e_374_, 1);
v_body_441_ = lean_ctor_get(v_e_374_, 2);
v_binderInfo_442_ = lean_ctor_get_uint8(v_e_374_, sizeof(void*)*3 + 8);
lean_inc(v_offset_375_);
lean_inc_ref(v_binderType_440_);
v___x_443_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_binderType_440_, v_offset_375_, v_a_376_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v___x_443_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_offset_375_, v___x_446_);
lean_dec(v_offset_375_);
lean_inc_ref(v_body_441_);
v___x_448_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_body_441_, v___x_447_, v_snd_445_);
v_fst_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_fst_449_);
v_snd_450_ = lean_ctor_get(v___x_448_, 1);
lean_inc(v_snd_450_);
lean_dec_ref(v___x_448_);
v___x_451_ = lean_ptr_addr(v_binderType_440_);
v___x_452_ = lean_ptr_addr(v_fst_444_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_inc(v_binderName_439_);
lean_dec_ref_known(v_e_374_, 3);
v___x_454_ = l_Lean_Expr_forallE___override(v_binderName_439_, v_fst_444_, v_fst_449_, v_binderInfo_442_);
v_fst_381_ = v___x_454_;
v_snd_382_ = v_snd_450_;
goto v___jp_380_;
}
else
{
size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_ptr_addr(v_body_441_);
v___x_456_ = lean_ptr_addr(v_fst_449_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_inc(v_binderName_439_);
lean_dec_ref_known(v_e_374_, 3);
v___x_458_ = l_Lean_Expr_forallE___override(v_binderName_439_, v_fst_444_, v_fst_449_, v_binderInfo_442_);
v_fst_381_ = v___x_458_;
v_snd_382_ = v_snd_450_;
goto v___jp_380_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_442_, v_binderInfo_442_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_inc(v_binderName_439_);
lean_dec_ref_known(v_e_374_, 3);
v___x_460_ = l_Lean_Expr_forallE___override(v_binderName_439_, v_fst_444_, v_fst_449_, v_binderInfo_442_);
v_fst_381_ = v___x_460_;
v_snd_382_ = v_snd_450_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_449_);
lean_dec(v_fst_444_);
v_fst_381_ = v_e_374_;
v_snd_382_ = v_snd_450_;
goto v___jp_380_;
}
}
}
}
case 8:
{
lean_object* v_declName_461_; lean_object* v_type_462_; lean_object* v_value_463_; lean_object* v_body_464_; uint8_t v_nondep_465_; lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_fst_475_; lean_object* v_snd_476_; size_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v_declName_461_ = lean_ctor_get(v_e_374_, 0);
v_type_462_ = lean_ctor_get(v_e_374_, 1);
v_value_463_ = lean_ctor_get(v_e_374_, 2);
v_body_464_ = lean_ctor_get(v_e_374_, 3);
v_nondep_465_ = lean_ctor_get_uint8(v_e_374_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_375_, 2);
lean_inc_ref(v_type_462_);
v___x_466_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_type_462_, v_offset_375_, v_a_376_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_466_);
lean_inc_ref(v_value_463_);
v___x_469_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_value_463_, v_offset_375_, v_snd_468_);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
lean_inc(v_snd_471_);
lean_dec_ref(v___x_469_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_offset_375_, v___x_472_);
lean_dec(v_offset_375_);
lean_inc_ref(v_body_464_);
v___x_474_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_body_464_, v___x_473_, v_snd_471_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_fst_475_);
v_snd_476_ = lean_ctor_get(v___x_474_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v___x_474_);
v___x_477_ = lean_ptr_addr(v_type_462_);
v___x_478_ = lean_ptr_addr(v_fst_467_);
v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_inc(v_declName_461_);
lean_dec_ref_known(v_e_374_, 4);
v___x_480_ = l_Lean_Expr_letE___override(v_declName_461_, v_fst_467_, v_fst_470_, v_fst_475_, v_nondep_465_);
v_fst_381_ = v___x_480_;
v_snd_382_ = v_snd_476_;
goto v___jp_380_;
}
else
{
size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_ptr_addr(v_value_463_);
v___x_482_ = lean_ptr_addr(v_fst_470_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_inc(v_declName_461_);
lean_dec_ref_known(v_e_374_, 4);
v___x_484_ = l_Lean_Expr_letE___override(v_declName_461_, v_fst_467_, v_fst_470_, v_fst_475_, v_nondep_465_);
v_fst_381_ = v___x_484_;
v_snd_382_ = v_snd_476_;
goto v___jp_380_;
}
else
{
size_t v___x_485_; size_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_ptr_addr(v_body_464_);
v___x_486_ = lean_ptr_addr(v_fst_475_);
v___x_487_ = lean_usize_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_declName_461_);
lean_dec_ref_known(v_e_374_, 4);
v___x_488_ = l_Lean_Expr_letE___override(v_declName_461_, v_fst_467_, v_fst_470_, v_fst_475_, v_nondep_465_);
v_fst_381_ = v___x_488_;
v_snd_382_ = v_snd_476_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_475_);
lean_dec(v_fst_470_);
lean_dec(v_fst_467_);
v_fst_381_ = v_e_374_;
v_snd_382_ = v_snd_476_;
goto v___jp_380_;
}
}
}
}
case 9:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref_known(v_e_374_, 1);
lean_dec(v_offset_375_);
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_490_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_489_, v_a_376_);
v___y_386_ = v___x_490_;
goto v___jp_385_;
}
case 10:
{
lean_object* v_data_491_; lean_object* v_expr_492_; lean_object* v___x_493_; lean_object* v_fst_494_; lean_object* v_snd_495_; size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v_data_491_ = lean_ctor_get(v_e_374_, 0);
v_expr_492_ = lean_ctor_get(v_e_374_, 1);
lean_inc_ref(v_expr_492_);
v___x_493_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_expr_492_, v_offset_375_, v_a_376_);
v_fst_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_fst_494_);
v_snd_495_ = lean_ctor_get(v___x_493_, 1);
lean_inc(v_snd_495_);
lean_dec_ref(v___x_493_);
v___x_496_ = lean_ptr_addr(v_expr_492_);
v___x_497_ = lean_ptr_addr(v_fst_494_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_inc(v_data_491_);
lean_dec_ref_known(v_e_374_, 2);
v___x_499_ = l_Lean_Expr_mdata___override(v_data_491_, v_fst_494_);
v_fst_381_ = v___x_499_;
v_snd_382_ = v_snd_495_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_494_);
v_fst_381_ = v_e_374_;
v_snd_382_ = v_snd_495_;
goto v___jp_380_;
}
}
default: 
{
lean_object* v_typeName_500_; lean_object* v_idx_501_; lean_object* v_struct_502_; lean_object* v___x_503_; lean_object* v_fst_504_; lean_object* v_snd_505_; size_t v___x_506_; size_t v___x_507_; uint8_t v___x_508_; 
v_typeName_500_ = lean_ctor_get(v_e_374_, 0);
v_idx_501_ = lean_ctor_get(v_e_374_, 1);
v_struct_502_ = lean_ctor_get(v_e_374_, 2);
lean_inc_ref(v_struct_502_);
v___x_503_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_struct_502_, v_offset_375_, v_a_376_);
v_fst_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_fst_504_);
v_snd_505_ = lean_ctor_get(v___x_503_, 1);
lean_inc(v_snd_505_);
lean_dec_ref(v___x_503_);
v___x_506_ = lean_ptr_addr(v_struct_502_);
v___x_507_ = lean_ptr_addr(v_fst_504_);
v___x_508_ = lean_usize_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_inc(v_idx_501_);
lean_inc(v_typeName_500_);
lean_dec_ref_known(v_e_374_, 3);
v___x_509_ = l_Lean_Expr_proj___override(v_typeName_500_, v_idx_501_, v_fst_504_);
v_fst_381_ = v___x_509_;
v_snd_382_ = v_snd_505_;
goto v___jp_380_;
}
else
{
lean_dec(v_fst_504_);
v_fst_381_ = v_e_374_;
v_snd_382_ = v_snd_505_;
goto v___jp_380_;
}
}
}
}
else
{
lean_object* v_val_510_; lean_object* v___x_511_; 
lean_dec_ref_known(v___x_379_, 2);
lean_dec(v_offset_375_);
lean_dec_ref(v_e_374_);
v_val_510_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_389_, 1);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_val_510_);
lean_ctor_set(v___x_511_, 1, v_a_376_);
return v___x_511_;
}
v___jp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_inc_ref(v_fst_381_);
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_382_, v___x_379_, v_fst_381_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_fst_381_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
v___jp_385_:
{
lean_object* v_fst_387_; lean_object* v_snd_388_; 
v_fst_387_ = lean_ctor_get(v___y_386_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v___y_386_, 1);
lean_inc(v_snd_388_);
lean_dec_ref(v___y_386_);
v_fst_381_ = v_fst_387_;
v_snd_382_ = v_snd_388_;
goto v___jp_380_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec(v_offset_375_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_e_374_);
lean_ctor_set(v___x_512_, 1, v_a_376_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_513_, lean_object* v_stop_514_, lean_object* v_args_515_, lean_object* v_offset_516_, size_t v_sz_517_, size_t v_i_518_, lean_object* v_bs_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_518_, v_sz_517_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v_offset_516_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_bs_519_);
lean_ctor_set(v___x_522_, 1, v___y_520_);
return v___x_522_;
}
else
{
lean_object* v_v_523_; lean_object* v___x_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v___x_527_; lean_object* v_bs_x27_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v_v_523_ = lean_array_uget_borrowed(v_bs_519_, v_i_518_);
lean_inc(v_offset_516_);
lean_inc(v_v_523_);
v___x_524_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_513_, v_stop_514_, v_args_515_, v_v_523_, v_offset_516_, v___y_520_);
v_fst_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_fst_525_);
v_snd_526_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_snd_526_);
lean_dec_ref(v___x_524_);
v___x_527_ = lean_unsigned_to_nat(0u);
v_bs_x27_528_ = lean_array_uset(v_bs_519_, v_i_518_, v___x_527_);
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_add(v_i_518_, v___x_529_);
v___x_531_ = lean_array_uset(v_bs_x27_528_, v_i_518_, v_fst_525_);
v_i_518_ = v___x_530_;
v_bs_519_ = v___x_531_;
v___y_520_ = v_snd_526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_533_, lean_object* v_stop_534_, lean_object* v_args_535_, lean_object* v_offset_536_, lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_, lean_object* v___y_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_542_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_533_, v_stop_534_, v_args_535_, v_offset_536_, v_sz_boxed_541_, v_i_boxed_542_, v_bs_539_, v___y_540_);
lean_dec_ref(v_args_535_);
lean_dec(v_stop_534_);
lean_dec(v_start_533_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_544_, lean_object* v_stop_545_, lean_object* v_args_546_, lean_object* v_e_547_, lean_object* v_offset_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_544_, v_stop_545_, v_args_546_, v_e_547_, v_offset_548_, v_a_549_);
lean_dec_ref(v_args_546_);
lean_dec(v_stop_545_);
lean_dec(v_start_544_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_551_, lean_object* v_stop_552_, lean_object* v_args_553_, lean_object* v_e_554_, lean_object* v_f_555_, lean_object* v_a_556_, lean_object* v_offset_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_551_, v_stop_552_, v_args_553_, v_e_554_, v_f_555_, v_a_556_, v_offset_557_, v_a_558_);
lean_dec_ref(v_args_553_);
lean_dec(v_stop_552_);
lean_dec(v_start_551_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_560_, lean_object* v_stop_561_, lean_object* v_args_562_, lean_object* v_e_563_, lean_object* v_offset_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_560_, v_stop_561_, v_args_562_, v_e_563_, v_offset_564_, v_a_565_);
lean_dec_ref(v_args_562_);
lean_dec(v_stop_561_);
lean_dec(v_start_560_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_568_, v_a_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_571_, v_m_572_, v_a_573_);
lean_dec_ref(v_a_573_);
lean_dec_ref(v_m_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_575_, lean_object* v_m_576_, lean_object* v_a_577_, lean_object* v_b_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_576_, v_a_577_, v_b_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_584_, v_a_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec_ref(v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_588_, lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_592_, lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_592_, v_a_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec_ref(v_a_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object* v_00_u03b2_597_, lean_object* v_data_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_data_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object* v_00_u03b2_600_, lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_601_, v_b_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_605_, lean_object* v_i_606_, lean_object* v_source_607_, lean_object* v_target_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v_i_606_, v_source_607_, v_target_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_x_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
v___x_619_ = l_Lean_Expr_consumeMData(v___x_618_);
v___x_620_ = l_Lean_Expr_isLambda(v___x_619_);
lean_dec_ref(v___x_619_);
if (v___x_620_ == 0)
{
size_t v___x_621_; size_t v___x_622_; 
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_615_, v___x_621_);
v_i_615_ = v___x_622_;
goto _start;
}
else
{
return v___x_620_;
}
}
else
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_625_, lean_object* v_i_626_, lean_object* v_stop_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; uint8_t v_res_630_; lean_object* v_r_631_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_626_);
lean_dec(v_i_626_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_627_);
lean_dec(v_stop_627_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_625_, v_i_boxed_628_, v_stop_boxed_629_);
lean_dec_ref(v_as_625_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_unsigned_to_nat(16u);
v___x_634_ = lean_mk_array(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__0, &l_Lean_Expr_instantiateBetaRevRange___closed__0_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__0);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__3));
v___x_641_ = lean_unsigned_to_nat(4u);
v___x_642_ = lean_unsigned_to_nat(39u);
v___x_643_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__2));
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_645_ = l_mkPanicMessageWithDecl(v___x_644_, v___x_643_, v___x_642_, v___x_641_, v___x_640_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_646_, lean_object* v_start_647_, lean_object* v_stop_648_, lean_object* v_args_649_){
_start:
{
lean_object* v___y_651_; uint8_t v___y_663_; uint8_t v___x_670_; 
v___x_670_ = l_Lean_Expr_hasLooseBVars(v_e_646_);
if (v___x_670_ == 0)
{
v___y_663_ = v___x_670_;
goto v___jp_662_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = lean_nat_dec_lt(v_start_647_, v_stop_648_);
v___y_663_ = v___x_671_;
goto v___jp_662_;
}
v___jp_650_:
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_lt(v_start_647_, v___y_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v___y_651_);
v___x_653_ = lean_expr_instantiate_rev_range(v_e_646_, v_start_647_, v_stop_648_, v_args_649_);
lean_dec(v_stop_648_);
lean_dec_ref(v_e_646_);
return v___x_653_;
}
else
{
size_t v___x_654_; size_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_usize_of_nat(v_start_647_);
v___x_655_ = lean_usize_of_nat(v___y_651_);
lean_dec(v___y_651_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_649_, v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_expr_instantiate_rev_range(v_e_646_, v_start_647_, v_stop_648_, v_args_649_);
lean_dec(v_stop_648_);
lean_dec_ref(v_e_646_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_fst_661_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__1, &l_Lean_Expr_instantiateBetaRevRange___closed__1_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__1);
v___x_660_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_647_, v_stop_648_, v_args_649_, v_e_646_, v___x_658_, v___x_659_);
lean_dec(v_stop_648_);
v_fst_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_fst_661_);
lean_dec_ref(v___x_660_);
return v_fst_661_;
}
}
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
lean_dec(v_stop_648_);
return v_e_646_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_array_get_size(v_args_649_);
v___x_665_ = lean_nat_dec_le(v_stop_648_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v_stop_648_);
lean_dec_ref(v_e_646_);
v___x_666_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_667_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_666_);
return v___x_667_;
}
else
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_lt(v_start_647_, v_stop_648_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_expr_instantiate_rev_range(v_e_646_, v_start_647_, v_stop_648_, v_args_649_);
lean_dec(v_stop_648_);
lean_dec_ref(v_e_646_);
return v___x_669_;
}
else
{
if (v___x_665_ == 0)
{
v___y_651_ = v___x_664_;
goto v___jp_650_;
}
else
{
lean_inc(v_stop_648_);
v___y_651_ = v_stop_648_;
goto v___jp_650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_672_, lean_object* v_start_673_, lean_object* v_stop_674_, lean_object* v_args_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Expr_instantiateBetaRevRange(v_e_672_, v_start_673_, v_stop_674_, v_args_675_);
lean_dec_ref(v_args_675_);
lean_dec(v_start_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; lean_object* v_env_684_; lean_object* v___x_685_; lean_object* v_mctx_686_; lean_object* v_lctx_687_; lean_object* v_options_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_683_ = lean_st_ref_get(v___y_681_);
v_env_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref(v_env_684_);
lean_dec(v___x_683_);
v___x_685_ = lean_st_ref_get(v___y_679_);
v_mctx_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_mctx_686_);
lean_dec(v___x_685_);
v_lctx_687_ = lean_ctor_get(v___y_678_, 2);
v_options_688_ = lean_ctor_get(v___y_680_, 2);
lean_inc_ref(v_options_688_);
lean_inc_ref(v_lctx_687_);
v___x_689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_689_, 0, v_env_684_);
lean_ctor_set(v___x_689_, 1, v_mctx_686_);
lean_ctor_set(v___x_689_, 2, v_lctx_687_);
lean_ctor_set(v___x_689_, 3, v_options_688_);
v___x_690_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_msgData_677_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_ref_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_ref_705_ = lean_ctor_get(v___y_702_, 5);
v___x_706_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_ref_705_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_ref_705_);
lean_ctor_set(v___x_711_, 1, v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_733_ = l_Lean_indentExpr(v_f_726_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_734_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_743_, lean_object* v_f_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_751_, lean_object* v_f_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_751_, v_f_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_767_, lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_767_, v_msg_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_775_, lean_object* v_args_776_, lean_object* v_f_777_, lean_object* v_a_778_, lean_object* v_b_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_a_786_; uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_lt(v_a_778_, v_upperBound_775_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v_a_778_);
lean_dec_ref(v_f_777_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_b_779_);
return v___x_791_;
}
else
{
lean_object* v_fst_792_; 
v_fst_792_ = lean_ctor_get(v_b_779_, 0);
lean_inc(v_fst_792_);
if (lean_obj_tag(v_fst_792_) == 7)
{
lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_snd_793_ = lean_ctor_get(v_b_779_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_b_779_, 0);
lean_dec(v_unused_802_);
v___x_795_ = v_b_779_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_dec(v_b_779_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_body_797_; lean_object* v___x_799_; 
v_body_797_ = lean_ctor_get(v_fst_792_, 2);
lean_inc_ref(v_body_797_);
lean_dec_ref_known(v_fst_792_, 3);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_body_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_body_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_793_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v_a_786_ = v___x_799_;
goto v___jp_785_;
}
}
}
else
{
lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_838_; 
v_snd_803_ = lean_ctor_get(v_b_779_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_779_, 0);
lean_dec(v_unused_839_);
v___x_805_ = v_b_779_;
v_isShared_806_ = v_isSharedCheck_838_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_dec(v_b_779_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_838_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_inc(v_a_778_);
lean_inc(v_fst_792_);
v___x_807_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_792_, v_snd_803_, v_a_778_, v_args_776_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
v___x_808_ = lean_whnf(v___x_807_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
if (lean_obj_tag(v_a_809_) == 7)
{
lean_object* v_body_810_; lean_object* v___x_812_; 
lean_dec(v_snd_803_);
lean_dec(v_fst_792_);
v_body_810_ = lean_ctor_get(v_a_809_, 2);
lean_inc_ref(v_body_810_);
lean_dec_ref_known(v_a_809_, 3);
lean_inc(v_a_778_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_a_778_);
lean_ctor_set(v___x_805_, 0, v_body_810_);
v___x_812_ = v___x_805_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_body_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_a_778_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_786_ = v___x_812_;
goto v___jp_785_;
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v_a_809_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_a_778_, v___x_815_);
lean_inc_ref(v_f_777_);
v___x_817_ = l_Lean_mkAppRange(v_f_777_, v___x_814_, v___x_816_, v_args_776_);
lean_dec(v___x_816_);
v___x_818_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_817_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v___x_820_; 
lean_dec_ref_known(v___x_818_, 1);
if (v_isShared_806_ == 0)
{
v___x_820_ = v___x_805_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_snd_803_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v_a_786_ = v___x_820_;
goto v___jp_785_;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_805_);
lean_dec(v_snd_803_);
lean_dec(v_fst_792_);
lean_dec(v_a_778_);
lean_dec_ref(v_f_777_);
v_a_822_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_818_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_del_object(v___x_805_);
lean_dec(v_snd_803_);
lean_dec(v_fst_792_);
lean_dec(v_a_778_);
lean_dec_ref(v_f_777_);
v_a_830_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_808_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_808_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_a_778_, v___x_787_);
lean_dec(v_a_778_);
v_a_778_ = v___x_788_;
v_b_779_ = v_a_786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_840_, lean_object* v_args_841_, lean_object* v_f_842_, lean_object* v_a_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_840_, v_args_841_, v_f_842_, v_a_843_, v_b_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v_args_841_);
lean_dec(v_upperBound_840_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_851_, lean_object* v_args_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
lean_inc(v_a_856_);
lean_inc_ref(v_a_855_);
lean_inc(v_a_854_);
lean_inc_ref(v_a_853_);
lean_inc_ref(v_f_851_);
v___x_858_ = lean_infer_type(v_f_851_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_array_get_size(v_args_852_);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_a_859_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_860_, v_args_852_, v_f_851_, v___x_861_, v___x_862_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v_fst_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_snd_869_);
lean_dec(v_a_864_);
v___x_870_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_868_, v_snd_869_, v___x_860_, v_args_852_);
lean_dec(v_snd_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_863_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_863_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_dec_ref(v_f_851_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_883_, lean_object* v_args_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_883_, v_args_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_args_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_891_, lean_object* v_args_892_, lean_object* v_f_893_, lean_object* v_inst_894_, lean_object* v_R_895_, lean_object* v_a_896_, lean_object* v_b_897_, lean_object* v_c_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_891_, v_args_892_, v_f_893_, v_a_896_, v_b_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_905_, lean_object* v_args_906_, lean_object* v_f_907_, lean_object* v_inst_908_, lean_object* v_R_909_, lean_object* v_a_910_, lean_object* v_b_911_, lean_object* v_c_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_905_, v_args_906_, v_f_907_, v_inst_908_, v_R_909_, v_a_910_, v_b_911_, v_c_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_args_906_);
lean_dec(v_upperBound_905_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_922_, lean_object* v_us_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_930_ = l_Lean_mkConst(v_constName_922_, v_us_923_);
v___x_931_ = l_Lean_MessageData_ofExpr(v___x_930_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_932_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_934_, lean_object* v_us_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_934_, v_us_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_942_, lean_object* v_constName_943_, lean_object* v_us_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_943_, v_us_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_951_, lean_object* v_constName_952_, lean_object* v_us_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_951_, v_constName_952_, v_us_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_960_, lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_fileName_967_; lean_object* v_fileMap_968_; lean_object* v_options_969_; lean_object* v_currRecDepth_970_; lean_object* v_maxRecDepth_971_; lean_object* v_ref_972_; lean_object* v_currNamespace_973_; lean_object* v_openDecls_974_; lean_object* v_initHeartbeats_975_; lean_object* v_maxHeartbeats_976_; lean_object* v_quotContext_977_; lean_object* v_currMacroScope_978_; uint8_t v_diag_979_; lean_object* v_cancelTk_x3f_980_; uint8_t v_suppressElabErrors_981_; lean_object* v_inheritedTraceOptions_982_; lean_object* v_ref_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_fileName_967_ = lean_ctor_get(v___y_964_, 0);
v_fileMap_968_ = lean_ctor_get(v___y_964_, 1);
v_options_969_ = lean_ctor_get(v___y_964_, 2);
v_currRecDepth_970_ = lean_ctor_get(v___y_964_, 3);
v_maxRecDepth_971_ = lean_ctor_get(v___y_964_, 4);
v_ref_972_ = lean_ctor_get(v___y_964_, 5);
v_currNamespace_973_ = lean_ctor_get(v___y_964_, 6);
v_openDecls_974_ = lean_ctor_get(v___y_964_, 7);
v_initHeartbeats_975_ = lean_ctor_get(v___y_964_, 8);
v_maxHeartbeats_976_ = lean_ctor_get(v___y_964_, 9);
v_quotContext_977_ = lean_ctor_get(v___y_964_, 10);
v_currMacroScope_978_ = lean_ctor_get(v___y_964_, 11);
v_diag_979_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*14);
v_cancelTk_x3f_980_ = lean_ctor_get(v___y_964_, 12);
v_suppressElabErrors_981_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_982_ = lean_ctor_get(v___y_964_, 13);
v_ref_983_ = l_Lean_replaceRef(v_ref_960_, v_ref_972_);
lean_inc_ref(v_inheritedTraceOptions_982_);
lean_inc(v_cancelTk_x3f_980_);
lean_inc(v_currMacroScope_978_);
lean_inc(v_quotContext_977_);
lean_inc(v_maxHeartbeats_976_);
lean_inc(v_initHeartbeats_975_);
lean_inc(v_openDecls_974_);
lean_inc(v_currNamespace_973_);
lean_inc(v_maxRecDepth_971_);
lean_inc(v_currRecDepth_970_);
lean_inc_ref(v_options_969_);
lean_inc_ref(v_fileMap_968_);
lean_inc_ref(v_fileName_967_);
v___x_984_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_984_, 0, v_fileName_967_);
lean_ctor_set(v___x_984_, 1, v_fileMap_968_);
lean_ctor_set(v___x_984_, 2, v_options_969_);
lean_ctor_set(v___x_984_, 3, v_currRecDepth_970_);
lean_ctor_set(v___x_984_, 4, v_maxRecDepth_971_);
lean_ctor_set(v___x_984_, 5, v_ref_983_);
lean_ctor_set(v___x_984_, 6, v_currNamespace_973_);
lean_ctor_set(v___x_984_, 7, v_openDecls_974_);
lean_ctor_set(v___x_984_, 8, v_initHeartbeats_975_);
lean_ctor_set(v___x_984_, 9, v_maxHeartbeats_976_);
lean_ctor_set(v___x_984_, 10, v_quotContext_977_);
lean_ctor_set(v___x_984_, 11, v_currMacroScope_978_);
lean_ctor_set(v___x_984_, 12, v_cancelTk_x3f_980_);
lean_ctor_set(v___x_984_, 13, v_inheritedTraceOptions_982_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*14, v_diag_979_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*14 + 1, v_suppressElabErrors_981_);
v___x_985_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_961_, v___y_962_, v___y_963_, v___x_984_, v___y_965_);
lean_dec_ref_known(v___x_984_, 14);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_986_, lean_object* v_msg_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_986_, v_msg_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_ref_986_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
lean_ctor_set(v___x_999_, 3, v___x_998_);
lean_ctor_set(v___x_999_, 4, v___x_997_);
lean_ctor_set(v___x_999_, 5, v___x_997_);
lean_ctor_set(v___x_999_, 6, v___x_997_);
lean_ctor_set(v___x_999_, 7, v___x_997_);
lean_ctor_set(v___x_999_, 8, v___x_997_);
lean_ctor_set(v___x_999_, 9, v___x_997_);
lean_ctor_set(v___x_999_, 10, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(32u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((size_t)5ULL);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_unsigned_to_nat(32u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1008_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1004_);
lean_ctor_set(v___x_1008_, 3, v___x_1004_);
lean_ctor_set_usize(v___x_1008_, 4, v___x_1003_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1009_ = lean_box(1);
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
lean_ctor_set(v___x_1012_, 2, v___x_1009_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1034_, lean_object* v_declHint_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_env_1039_; uint8_t v___x_1040_; 
v___x_1038_ = lean_st_ref_get(v___y_1036_);
v_env_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_env_1039_);
lean_dec(v___x_1038_);
v___x_1040_ = l_Lean_Name_isAnonymous(v_declHint_1035_);
if (v___x_1040_ == 0)
{
uint8_t v_isExporting_1041_; 
v_isExporting_1041_ = lean_ctor_get_uint8(v_env_1039_, sizeof(void*)*8);
if (v_isExporting_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_env_1039_);
lean_dec(v_declHint_1035_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_msg_1034_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
lean_inc_ref(v_env_1039_);
v___x_1043_ = l_Lean_Environment_setExporting(v_env_1039_, v___x_1040_);
lean_inc(v_declHint_1035_);
lean_inc_ref(v___x_1043_);
v___x_1044_ = l_Lean_Environment_contains(v___x_1043_, v_declHint_1035_, v_isExporting_1041_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_env_1039_);
lean_dec(v_declHint_1035_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_msg_1034_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_c_1051_; lean_object* v___x_1052_; 
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1048_ = l_Lean_Options_empty;
v___x_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1043_);
lean_ctor_set(v___x_1049_, 1, v___x_1046_);
lean_ctor_set(v___x_1049_, 2, v___x_1047_);
lean_ctor_set(v___x_1049_, 3, v___x_1048_);
lean_inc(v_declHint_1035_);
v___x_1050_ = l_Lean_MessageData_ofConstName(v_declHint_1035_, v___x_1040_);
v_c_1051_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1051_, 0, v___x_1049_);
lean_ctor_set(v_c_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1039_, v_declHint_1035_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v_env_1039_);
lean_dec(v_declHint_1035_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_c_1051_);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_note(v___x_1056_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_msg_1034_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v_val_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1095_; 
v_val_1060_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1062_ = v___x_1052_;
v_isShared_1063_ = v_isSharedCheck_1095_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_val_1060_);
lean_dec(v___x_1052_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1095_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_mod_1067_; uint8_t v___x_1068_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = l_Lean_Environment_header(v_env_1039_);
lean_dec_ref(v_env_1039_);
v___x_1066_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1065_);
v_mod_1067_ = lean_array_get(v___x_1064_, v___x_1066_, v_val_1060_);
lean_dec(v_val_1060_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = l_Lean_isPrivateName(v_declHint_1035_);
lean_dec(v_declHint_1035_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_c_1051_);
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_MessageData_ofName(v_mod_1067_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_note(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_msg_1034_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1078_);
v___x_1080_ = v___x_1062_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_c_1051_);
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_ofName(v_mod_1067_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_MessageData_note(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_msg_1034_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1091_);
v___x_1093_ = v___x_1062_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1096_; 
lean_dec_ref(v_env_1039_);
lean_dec(v_declHint_1035_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_msg_1034_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1097_, lean_object* v_declHint_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1097_, v_declHint_1098_, v___y_1099_);
lean_dec(v___y_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1102_, lean_object* v_declHint_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v___x_1109_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1102_, v_declHint_1103_, v___y_1107_);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = l_Lean_unknownIdentifierMessageTag;
v___x_1115_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v_a_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1120_, lean_object* v_declHint_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1120_, v_declHint_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1128_, lean_object* v_msg_1129_, lean_object* v_declHint_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v_a_1137_; lean_object* v___x_1138_; 
v___x_1136_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1129_, v_declHint_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1128_, v_a_1137_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1139_, lean_object* v_msg_1140_, lean_object* v_declHint_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1139_, v_msg_1140_, v_declHint_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v_ref_1139_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1154_, lean_object* v_constName_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1161_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1162_ = 0;
lean_inc(v_constName_1155_);
v___x_1163_ = l_Lean_MessageData_ofConstName(v_constName_1155_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1154_, v___x_1166_, v_constName_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1168_, lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1168_, v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v_ref_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_ref_1182_; lean_object* v___x_1183_; 
v_ref_1182_ = lean_ctor_get(v___y_1179_, 5);
v___x_1183_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1182_, v_constName_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v_env_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_st_ref_get(v___y_1195_);
v_env_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc_ref(v_env_1198_);
lean_dec(v___x_1197_);
v___x_1199_ = 0;
lean_inc(v_constName_1191_);
v___x_1200_ = l_Lean_Environment_findConstVal_x3f(v_env_1198_, v_constName_1191_, v___x_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1201_;
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_constName_1191_);
v_val_1202_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_val_1202_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 0);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_val_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1217_, lean_object* v_us_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc(v_c_1217_);
v___x_1224_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1217_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_levelParams_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_levelParams_1226_ = lean_ctor_get(v_a_1225_, 1);
v___x_1227_ = l_List_lengthTR___redArg(v_levelParams_1226_);
v___x_1228_ = l_List_lengthTR___redArg(v_us_1218_);
v___x_1229_ = lean_nat_dec_eq(v___x_1227_, v___x_1228_);
lean_dec(v___x_1228_);
lean_dec(v___x_1227_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec(v_a_1225_);
v___x_1230_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1217_, v_us_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_c_1217_);
v___x_1231_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1225_, v_us_1218_, v_a_1222_);
return v___x_1231_;
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_us_1218_);
lean_dec(v_c_1217_);
v_a_1232_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1240_, lean_object* v_us_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1240_, v_us_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_constName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1256_, v_constName_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1264_, lean_object* v_ref_1265_, lean_object* v_constName_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1265_, v_constName_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_ref_1274_, lean_object* v_constName_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1273_, v_ref_1274_, v_constName_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v_ref_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v_declHint_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1283_, v_msg_1284_, v_declHint_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1292_, v_ref_1293_, v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v_ref_1293_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1302_, lean_object* v_declHint_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1302_, v_declHint_1303_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1310_, lean_object* v_declHint_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1310_, v_declHint_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1319_, v_msg_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_ref_1328_, lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1327_, v_ref_1328_, v_msg_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v_ref_1328_);
return v_res_1335_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1342_, lean_object* v_idx_1343_, lean_object* v_e_1344_, lean_object* v_a_1345_, lean_object* v_00_u03b1_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1354_ = l_Lean_mkProj(v_structName_1342_, v_idx_1343_, v_e_1344_);
v___x_1355_ = l_Lean_indentExpr(v___x_1354_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_indentExpr(v_a_1345_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1360_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1362_, lean_object* v_idx_1363_, lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_00_u03b1_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1362_, v_idx_1363_, v_e_1364_, v_a_1365_, v_00_u03b1_1366_, v_x_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v_env_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_st_ref_get(v___y_1378_);
v_env_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1380_);
v___x_1382_ = 0;
lean_inc(v_constName_1374_);
v___x_1383_ = l_Lean_Environment_find_x3f(v_env_1381_, v_constName_1374_, v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1384_;
}
else
{
lean_object* v_val_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_constName_1374_);
v_val_1385_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1383_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_val_1385_);
lean_dec(v___x_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 0);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_val_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1400_, lean_object* v_structName_1401_, lean_object* v_e_1402_, lean_object* v_idx_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_a_1413_; uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_lt(v_a_1405_, v_upperBound_1400_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_idx_1403_);
lean_dec_ref(v_e_1402_);
lean_dec(v_structName_1401_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_b_1406_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
v___x_1419_ = lean_whnf(v_b_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
if (lean_obj_tag(v_a_1420_) == 7)
{
lean_object* v_body_1421_; uint8_t v___x_1422_; 
v_body_1421_ = lean_ctor_get(v_a_1420_, 2);
lean_inc_ref(v_body_1421_);
lean_dec_ref_known(v_a_1420_, 3);
v___x_1422_ = l_Lean_Expr_hasLooseBVars(v_body_1421_);
if (v___x_1422_ == 0)
{
v_a_1413_ = v_body_1421_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_inc_ref(v_e_1402_);
lean_inc(v_a_1405_);
lean_inc(v_structName_1401_);
v___x_1423_ = l_Lean_mkProj(v_structName_1401_, v_a_1405_, v_e_1402_);
v___x_1424_ = lean_expr_instantiate1(v_body_1421_, v___x_1423_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v_body_1421_);
v_a_1413_ = v___x_1424_;
goto v___jp_1412_;
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1425_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1402_);
lean_inc(v_idx_1403_);
lean_inc(v_structName_1401_);
v___x_1426_ = l_Lean_mkProj(v_structName_1401_, v_idx_1403_, v_e_1402_);
v___x_1427_ = l_Lean_indentExpr(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc_ref(v_a_1404_);
v___x_1431_ = l_Lean_indentExpr(v_a_1404_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1432_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
v_a_1413_ = v_a_1420_;
goto v___jp_1412_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1420_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_idx_1403_);
lean_dec_ref(v_e_1402_);
lean_dec(v_structName_1401_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_idx_1403_);
lean_dec_ref(v_e_1402_);
lean_dec(v_structName_1401_);
return v___x_1419_;
}
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_unsigned_to_nat(1u);
v___x_1415_ = lean_nat_add(v_a_1405_, v___x_1414_);
lean_dec(v_a_1405_);
v_a_1405_ = v___x_1415_;
v_b_1406_ = v_a_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1442_, lean_object* v_structName_1443_, lean_object* v_e_1444_, lean_object* v_idx_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1442_, v_structName_1443_, v_e_1444_, v_idx_1445_, v_a_1446_, v_a_1447_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v_upperBound_1442_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1455_, lean_object* v_structName_1456_, lean_object* v_e_1457_, lean_object* v_idx_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_a_1468_; uint8_t v___x_1472_; 
v___x_1472_ = lean_nat_dec_lt(v_a_1460_, v_upperBound_1455_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_idx_1458_);
lean_dec_ref(v_e_1457_);
lean_dec(v_structName_1456_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1461_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; 
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
v___x_1474_ = lean_whnf(v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
if (lean_obj_tag(v_a_1475_) == 7)
{
lean_object* v_body_1476_; uint8_t v___x_1477_; 
v_body_1476_ = lean_ctor_get(v_a_1475_, 2);
lean_inc_ref(v_body_1476_);
lean_dec_ref_known(v_a_1475_, 3);
v___x_1477_ = l_Lean_Expr_hasLooseBVars(v_body_1476_);
if (v___x_1477_ == 0)
{
v_a_1468_ = v_body_1476_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_inc_ref(v_e_1457_);
lean_inc(v_a_1460_);
lean_inc(v_structName_1456_);
v___x_1478_ = l_Lean_mkProj(v_structName_1456_, v_a_1460_, v_e_1457_);
v___x_1479_ = lean_expr_instantiate1(v_body_1476_, v___x_1478_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v_body_1476_);
v_a_1468_ = v___x_1479_;
goto v___jp_1467_;
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1457_);
lean_inc(v_idx_1458_);
lean_inc(v_structName_1456_);
v___x_1481_ = l_Lean_mkProj(v_structName_1456_, v_idx_1458_, v_e_1457_);
v___x_1482_ = l_Lean_indentExpr(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1480_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc_ref(v_a_1459_);
v___x_1486_ = l_Lean_indentExpr(v_a_1459_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1487_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_dec_ref_known(v___x_1488_, 1);
v_a_1468_ = v_a_1475_;
goto v___jp_1467_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1475_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_idx_1458_);
lean_dec_ref(v_e_1457_);
lean_dec(v_structName_1456_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_idx_1458_);
lean_dec_ref(v_e_1457_);
lean_dec(v_structName_1456_);
return v___x_1474_;
}
}
v___jp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v_a_1460_, v___x_1469_);
lean_dec(v_a_1460_);
v___x_1471_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1455_, v_structName_1456_, v_e_1457_, v_idx_1458_, v_a_1459_, v___x_1470_, v_a_1468_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1497_, lean_object* v_structName_1498_, lean_object* v_e_1499_, lean_object* v_idx_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1497_, v_structName_1498_, v_e_1499_, v_idx_1500_, v_a_1501_, v_a_1502_, v_b_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v_upperBound_1497_);
return v_res_1509_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1510_; lean_object* v_dummy_1511_; 
v___x_1510_ = lean_box(0);
v_dummy_1511_ = l_Lean_Expr_sort___override(v___x_1510_);
return v_dummy_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1512_, lean_object* v_idx_1513_, lean_object* v_e_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
lean_inc(v_a_1516_);
lean_inc_ref(v_a_1515_);
lean_inc_ref(v_e_1514_);
v___x_1520_ = lean_infer_type(v_e_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
lean_inc(v_a_1516_);
lean_inc_ref(v_a_1515_);
v___x_1522_ = lean_whnf(v_a_1521_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Expr_getAppFn(v_a_1523_);
if (lean_obj_tag(v___x_1524_) == 4)
{
lean_object* v_declName_1525_; lean_object* v_us_1526_; lean_object* v___x_1527_; lean_object* v_env_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; 
v_declName_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_declName_1525_);
v_us_1526_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_us_1526_);
lean_dec_ref_known(v___x_1524_, 2);
v___x_1527_ = lean_st_ref_get(v_a_1518_);
v_env_1531_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1531_);
lean_dec(v___x_1527_);
v___x_1532_ = 0;
v___x_1533_ = l_Lean_Environment_find_x3f(v_env_1531_, v_declName_1525_, v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_us_1526_);
v___x_1534_ = lean_box(0);
v___x_1535_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1534_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1535_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1533_, 1);
if (lean_obj_tag(v_val_1536_) == 5)
{
lean_object* v_val_1537_; lean_object* v_ctors_1538_; 
v_val_1537_ = lean_ctor_get(v_val_1536_, 0);
lean_inc_ref(v_val_1537_);
lean_dec_ref_known(v_val_1536_, 1);
v_ctors_1538_ = lean_ctor_get(v_val_1537_, 4);
lean_inc(v_ctors_1538_);
if (lean_obj_tag(v_ctors_1538_) == 1)
{
lean_object* v_tail_1539_; 
v_tail_1539_ = lean_ctor_get(v_ctors_1538_, 1);
if (lean_obj_tag(v_tail_1539_) == 0)
{
lean_object* v_toConstantVal_1540_; lean_object* v_numParams_1541_; lean_object* v_numIndices_1542_; lean_object* v_head_1543_; lean_object* v___x_1544_; 
v_toConstantVal_1540_ = lean_ctor_get(v_val_1537_, 0);
lean_inc_ref(v_toConstantVal_1540_);
v_numParams_1541_ = lean_ctor_get(v_val_1537_, 1);
lean_inc(v_numParams_1541_);
v_numIndices_1542_ = lean_ctor_get(v_val_1537_, 2);
lean_inc(v_numIndices_1542_);
lean_dec_ref(v_val_1537_);
v_head_1543_ = lean_ctor_get(v_ctors_1538_, 0);
lean_inc(v_head_1543_);
lean_dec_ref_known(v_ctors_1538_, 2);
v___x_1544_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1543_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
if (lean_obj_tag(v_a_1545_) == 6)
{
lean_object* v_val_1546_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_name_1586_; uint8_t v___x_1587_; 
v_val_1546_ = lean_ctor_get(v_a_1545_, 0);
lean_inc_ref(v_val_1546_);
lean_dec_ref_known(v_a_1545_, 1);
v_name_1586_ = lean_ctor_get(v_toConstantVal_1540_, 0);
lean_inc(v_name_1586_);
lean_dec_ref(v_toConstantVal_1540_);
v___x_1587_ = lean_name_eq(v_name_1586_, v_structName_1512_);
lean_dec(v_name_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_val_1546_);
lean_dec(v_numIndices_1542_);
lean_dec(v_numParams_1541_);
lean_dec(v_us_1526_);
v___x_1588_ = lean_box(0);
v___x_1589_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1588_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
v___y_1548_ = v_a_1515_;
v___y_1549_ = v_a_1516_;
v___y_1550_ = v_a_1517_;
v___y_1551_ = v_a_1518_;
goto v___jp_1547_;
}
v___jp_1547_:
{
lean_object* v_dummy_1552_; lean_object* v_nargs_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_dummy_1552_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1553_ = l_Lean_Expr_getAppNumArgs(v_a_1523_);
lean_inc(v_nargs_1553_);
v___x_1554_ = lean_mk_array(v_nargs_1553_, v_dummy_1552_);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_sub(v_nargs_1553_, v___x_1555_);
lean_dec(v_nargs_1553_);
lean_inc(v_a_1523_);
v___x_1557_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1523_, v___x_1554_, v___x_1556_);
v___x_1558_ = lean_nat_add(v_numParams_1541_, v_numIndices_1542_);
lean_dec(v_numIndices_1542_);
v___x_1559_ = lean_array_get_size(v___x_1557_);
v___x_1560_ = lean_nat_dec_eq(v___x_1558_, v___x_1559_);
lean_dec(v___x_1558_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v___x_1557_);
lean_dec_ref(v_val_1546_);
lean_dec(v_numParams_1541_);
lean_dec(v_us_1526_);
v___x_1561_ = lean_box(0);
v___x_1562_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1561_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1562_;
}
else
{
lean_object* v_toConstantVal_1563_; lean_object* v_name_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_toConstantVal_1563_ = lean_ctor_get(v_val_1546_, 0);
lean_inc_ref(v_toConstantVal_1563_);
lean_dec_ref(v_val_1546_);
v_name_1564_ = lean_ctor_get(v_toConstantVal_1563_, 0);
lean_inc(v_name_1564_);
lean_dec_ref(v_toConstantVal_1563_);
v___x_1565_ = l_Lean_mkConst(v_name_1564_, v_us_1526_);
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = l_Array_toSubarray___redArg(v___x_1557_, v___x_1566_, v_numParams_1541_);
v___x_1568_ = l_Subarray_copy___redArg(v___x_1567_);
v___x_1569_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1565_, v___x_1568_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec_ref(v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
lean_inc(v_a_1523_);
lean_inc_ref(v_e_1514_);
lean_inc(v_structName_1512_);
lean_inc(v_idx_1513_);
v___x_1571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1513_, v_structName_1512_, v_e_1514_, v_idx_1513_, v_a_1523_, v___x_1566_, v_a_1570_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
v___x_1573_ = lean_whnf(v_a_1572_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1585_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1585_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1585_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
if (lean_obj_tag(v_a_1574_) == 7)
{
lean_object* v_binderType_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
v_binderType_1578_ = lean_ctor_get(v_a_1574_, 1);
lean_inc_ref(v_binderType_1578_);
lean_dec_ref_known(v_a_1574_, 3);
v___x_1579_ = lean_expr_consume_type_annotations(v_binderType_1578_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1576_);
lean_dec(v_a_1574_);
v___x_1583_ = lean_box(0);
v___x_1584_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1583_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1584_;
}
}
}
else
{
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
return v___x_1573_;
}
}
else
{
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
return v___x_1571_;
}
}
else
{
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
return v___x_1569_;
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_a_1545_);
lean_dec(v_numIndices_1542_);
lean_dec(v_numParams_1541_);
lean_dec_ref(v_toConstantVal_1540_);
lean_dec(v_us_1526_);
v___x_1598_ = lean_box(0);
v___x_1599_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1598_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1599_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_numIndices_1542_);
lean_dec(v_numParams_1541_);
lean_dec_ref(v_toConstantVal_1540_);
lean_dec(v_us_1526_);
lean_dec(v_a_1523_);
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
v_a_1600_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1544_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1544_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1538_, 2);
lean_dec_ref(v_val_1537_);
lean_dec(v_us_1526_);
goto v___jp_1528_;
}
}
else
{
lean_dec(v_ctors_1538_);
lean_dec_ref(v_val_1537_);
lean_dec(v_us_1526_);
goto v___jp_1528_;
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec(v_val_1536_);
lean_dec(v_us_1526_);
v___x_1608_ = lean_box(0);
v___x_1609_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1608_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1609_;
}
}
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1529_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1530_;
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v___x_1524_);
v___x_1610_ = lean_box(0);
v___x_1611_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1512_, v_idx_1513_, v_e_1514_, v_a_1523_, lean_box(0), v___x_1610_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1611_;
}
}
else
{
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
return v___x_1522_;
}
}
else
{
lean_dec_ref(v_e_1514_);
lean_dec(v_idx_1513_);
lean_dec(v_structName_1512_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1612_, lean_object* v_idx_1613_, lean_object* v_e_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1612_, v_idx_1613_, v_e_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1621_, lean_object* v_structName_1622_, lean_object* v_e_1623_, lean_object* v_idx_1624_, lean_object* v_a_1625_, lean_object* v_inst_1626_, lean_object* v_R_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_, lean_object* v_c_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1621_, v_structName_1622_, v_e_1623_, v_idx_1624_, v_a_1625_, v_a_1628_, v_b_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1637_, lean_object* v_structName_1638_, lean_object* v_e_1639_, lean_object* v_idx_1640_, lean_object* v_a_1641_, lean_object* v_inst_1642_, lean_object* v_R_1643_, lean_object* v_a_1644_, lean_object* v_b_1645_, lean_object* v_c_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1637_, v_structName_1638_, v_e_1639_, v_idx_1640_, v_a_1641_, v_inst_1642_, v_R_1643_, v_a_1644_, v_b_1645_, v_c_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_upperBound_1637_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1653_, lean_object* v_structName_1654_, lean_object* v_e_1655_, lean_object* v_idx_1656_, lean_object* v_a_1657_, lean_object* v_inst_1658_, lean_object* v_R_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_, lean_object* v_c_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1653_, v_structName_1654_, v_e_1655_, v_idx_1656_, v_a_1657_, v_a_1660_, v_b_1661_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1669_, lean_object* v_structName_1670_, lean_object* v_e_1671_, lean_object* v_idx_1672_, lean_object* v_a_1673_, lean_object* v_inst_1674_, lean_object* v_R_1675_, lean_object* v_a_1676_, lean_object* v_b_1677_, lean_object* v_c_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1669_, v_structName_1670_, v_e_1671_, v_idx_1672_, v_a_1673_, v_inst_1674_, v_R_1675_, v_a_1676_, v_b_1677_, v_c_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_upperBound_1669_);
return v_res_1684_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1695_ = l_Lean_indentExpr(v_type_1688_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1696_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1705_, lean_object* v_type_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_type_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1713_, v_type_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_ks_1725_; lean_object* v_vs_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1750_; 
v_ks_1725_ = lean_ctor_get(v_x_1721_, 0);
v_vs_1726_ = lean_ctor_get(v_x_1721_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_x_1721_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1728_ = v_x_1721_;
v_isShared_1729_ = v_isSharedCheck_1750_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_vs_1726_);
lean_inc(v_ks_1725_);
lean_dec(v_x_1721_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1750_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_array_get_size(v_ks_1725_);
v___x_1731_ = lean_nat_dec_lt(v_x_1722_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
lean_dec(v_x_1722_);
v___x_1732_ = lean_array_push(v_ks_1725_, v_x_1723_);
v___x_1733_ = lean_array_push(v_vs_1726_, v_x_1724_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1733_);
lean_ctor_set(v___x_1728_, 0, v___x_1732_);
v___x_1735_ = v___x_1728_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
else
{
lean_object* v_k_x27_1737_; uint8_t v___x_1738_; 
v_k_x27_1737_ = lean_array_fget_borrowed(v_ks_1725_, v_x_1722_);
v___x_1738_ = l_Lean_instBEqMVarId_beq(v_x_1723_, v_k_x27_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1740_; 
if (v_isShared_1729_ == 0)
{
v___x_1740_ = v___x_1728_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_ks_1725_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_vs_1726_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_nat_add(v_x_1722_, v___x_1741_);
lean_dec(v_x_1722_);
v_x_1721_ = v___x_1740_;
v_x_1722_ = v___x_1742_;
goto _start;
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1745_ = lean_array_fset(v_ks_1725_, v_x_1722_, v_x_1723_);
v___x_1746_ = lean_array_fset(v_vs_1726_, v_x_1722_, v_x_1724_);
lean_dec(v_x_1722_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1746_);
lean_ctor_set(v___x_1728_, 0, v___x_1745_);
v___x_1748_ = v___x_1728_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1751_, lean_object* v_k_1752_, lean_object* v_v_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1751_, v___x_1754_, v_k_1752_, v_v_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1757_, size_t v_x_1758_, size_t v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
if (lean_obj_tag(v_x_1757_) == 0)
{
lean_object* v_es_1762_; size_t v___x_1763_; size_t v___x_1764_; lean_object* v_j_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_es_1762_ = lean_ctor_get(v_x_1757_, 0);
v___x_1763_ = ((size_t)31ULL);
v___x_1764_ = lean_usize_land(v_x_1758_, v___x_1763_);
v_j_1765_ = lean_usize_to_nat(v___x_1764_);
v___x_1766_ = lean_array_get_size(v_es_1762_);
v___x_1767_ = lean_nat_dec_lt(v_j_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_dec(v_j_1765_);
lean_dec(v_x_1761_);
lean_dec(v_x_1760_);
return v_x_1757_;
}
else
{
lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1806_; 
lean_inc_ref(v_es_1762_);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1757_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_x_1757_, 0);
lean_dec(v_unused_1807_);
v___x_1769_ = v_x_1757_;
v_isShared_1770_ = v_isSharedCheck_1806_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v_x_1757_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1806_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_v_1771_; lean_object* v___x_1772_; lean_object* v_xs_x27_1773_; lean_object* v___y_1775_; 
v_v_1771_ = lean_array_fget(v_es_1762_, v_j_1765_);
v___x_1772_ = lean_box(0);
v_xs_x27_1773_ = lean_array_fset(v_es_1762_, v_j_1765_, v___x_1772_);
switch(lean_obj_tag(v_v_1771_))
{
case 0:
{
lean_object* v_key_1780_; lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1791_; 
v_key_1780_ = lean_ctor_get(v_v_1771_, 0);
v_val_1781_ = lean_ctor_get(v_v_1771_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_v_1771_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1783_ = v_v_1771_;
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_inc(v_key_1780_);
lean_dec(v_v_1771_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Lean_instBEqMVarId_beq(v_x_1760_, v_key_1780_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_del_object(v___x_1783_);
v___x_1786_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1780_, v_val_1781_, v_x_1760_, v_x_1761_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
v___y_1775_ = v___x_1787_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_val_1781_);
lean_dec(v_key_1780_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v_x_1761_);
lean_ctor_set(v___x_1783_, 0, v_x_1760_);
v___x_1789_ = v___x_1783_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_x_1760_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_x_1761_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v___y_1775_ = v___x_1789_;
goto v___jp_1774_;
}
}
}
}
case 1:
{
lean_object* v_node_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1804_; 
v_node_1792_ = lean_ctor_get(v_v_1771_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_v_1771_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1794_ = v_v_1771_;
v_isShared_1795_ = v_isSharedCheck_1804_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_node_1792_);
lean_dec(v_v_1771_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1804_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
size_t v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1796_ = ((size_t)5ULL);
v___x_1797_ = lean_usize_shift_right(v_x_1758_, v___x_1796_);
v___x_1798_ = ((size_t)1ULL);
v___x_1799_ = lean_usize_add(v_x_1759_, v___x_1798_);
v___x_1800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1792_, v___x_1797_, v___x_1799_, v_x_1760_, v_x_1761_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1800_);
v___x_1802_ = v___x_1794_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
v___y_1775_ = v___x_1802_;
goto v___jp_1774_;
}
}
}
default: 
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_x_1760_);
lean_ctor_set(v___x_1805_, 1, v_x_1761_);
v___y_1775_ = v___x_1805_;
goto v___jp_1774_;
}
}
v___jp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_array_fset(v_xs_x27_1773_, v_j_1765_, v___y_1775_);
lean_dec(v_j_1765_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1776_);
v___x_1778_ = v___x_1769_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
lean_object* v_ks_1808_; lean_object* v_vs_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1827_; 
v_ks_1808_ = lean_ctor_get(v_x_1757_, 0);
v_vs_1809_ = lean_ctor_get(v_x_1757_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_x_1757_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1811_ = v_x_1757_;
v_isShared_1812_ = v_isSharedCheck_1827_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_vs_1809_);
lean_inc(v_ks_1808_);
lean_dec(v_x_1757_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1827_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_ks_1808_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_vs_1809_);
v___x_1814_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v_newNode_1815_; size_t v___x_1816_; uint8_t v___x_1817_; 
v_newNode_1815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1814_, v_x_1760_, v_x_1761_);
v___x_1816_ = ((size_t)7ULL);
v___x_1817_ = lean_usize_dec_le(v___x_1816_, v_x_1759_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1815_);
v___x_1819_ = lean_unsigned_to_nat(4u);
v___x_1820_ = lean_nat_dec_lt(v___x_1818_, v___x_1819_);
lean_dec(v___x_1818_);
if (v___x_1820_ == 0)
{
lean_object* v_ks_1821_; lean_object* v_vs_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_ks_1821_ = lean_ctor_get(v_newNode_1815_, 0);
lean_inc_ref(v_ks_1821_);
v_vs_1822_ = lean_ctor_get(v_newNode_1815_, 1);
lean_inc_ref(v_vs_1822_);
lean_dec_ref(v_newNode_1815_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1759_, v_ks_1821_, v_vs_1822_, v___x_1823_, v___x_1824_);
lean_dec_ref(v_vs_1822_);
lean_dec_ref(v_ks_1821_);
return v___x_1825_;
}
else
{
return v_newNode_1815_;
}
}
else
{
return v_newNode_1815_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1828_, lean_object* v_keys_1829_, lean_object* v_vals_1830_, lean_object* v_i_1831_, lean_object* v_entries_1832_){
_start:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v_keys_1829_);
v___x_1834_ = lean_nat_dec_lt(v_i_1831_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec(v_i_1831_);
return v_entries_1832_;
}
else
{
lean_object* v_k_1835_; lean_object* v_v_1836_; uint64_t v___x_1837_; size_t v_h_1838_; size_t v___x_1839_; lean_object* v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; size_t v___x_1843_; size_t v_h_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_k_1835_ = lean_array_fget_borrowed(v_keys_1829_, v_i_1831_);
v_v_1836_ = lean_array_fget_borrowed(v_vals_1830_, v_i_1831_);
v___x_1837_ = l_Lean_instHashableMVarId_hash(v_k_1835_);
v_h_1838_ = lean_uint64_to_usize(v___x_1837_);
v___x_1839_ = ((size_t)5ULL);
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_sub(v_depth_1828_, v___x_1841_);
v___x_1843_ = lean_usize_mul(v___x_1839_, v___x_1842_);
v_h_1844_ = lean_usize_shift_right(v_h_1838_, v___x_1843_);
v___x_1845_ = lean_nat_add(v_i_1831_, v___x_1840_);
lean_dec(v_i_1831_);
lean_inc(v_v_1836_);
lean_inc(v_k_1835_);
v___x_1846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1832_, v_h_1844_, v_depth_1828_, v_k_1835_, v_v_1836_);
v_i_1831_ = v___x_1845_;
v_entries_1832_ = v___x_1846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1848_, lean_object* v_keys_1849_, lean_object* v_vals_1850_, lean_object* v_i_1851_, lean_object* v_entries_1852_){
_start:
{
size_t v_depth_boxed_1853_; lean_object* v_res_1854_; 
v_depth_boxed_1853_ = lean_unbox_usize(v_depth_1848_);
lean_dec(v_depth_1848_);
v_res_1854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1853_, v_keys_1849_, v_vals_1850_, v_i_1851_, v_entries_1852_);
lean_dec_ref(v_vals_1850_);
lean_dec_ref(v_keys_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
size_t v_x_1146__boxed_1860_; size_t v_x_1147__boxed_1861_; lean_object* v_res_1862_; 
v_x_1146__boxed_1860_ = lean_unbox_usize(v_x_1856_);
lean_dec(v_x_1856_);
v_x_1147__boxed_1861_ = lean_unbox_usize(v_x_1857_);
lean_dec(v_x_1857_);
v_res_1862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1855_, v_x_1146__boxed_1860_, v_x_1147__boxed_1861_, v_x_1858_, v_x_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
uint64_t v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = l_Lean_instHashableMVarId_hash(v_x_1864_);
v___x_1867_ = lean_uint64_to_usize(v___x_1866_);
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1863_, v___x_1867_, v___x_1868_, v_x_1864_, v_x_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1870_, lean_object* v_val_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_mctx_1875_; lean_object* v_cache_1876_; lean_object* v_zetaDeltaFVarIds_1877_; lean_object* v_postponed_1878_; lean_object* v_diag_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1908_; 
v___x_1874_ = lean_st_ref_take(v___y_1872_);
v_mctx_1875_ = lean_ctor_get(v___x_1874_, 0);
v_cache_1876_ = lean_ctor_get(v___x_1874_, 1);
v_zetaDeltaFVarIds_1877_ = lean_ctor_get(v___x_1874_, 2);
v_postponed_1878_ = lean_ctor_get(v___x_1874_, 3);
v_diag_1879_ = lean_ctor_get(v___x_1874_, 4);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1881_ = v___x_1874_;
v_isShared_1882_ = v_isSharedCheck_1908_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_diag_1879_);
lean_inc(v_postponed_1878_);
lean_inc(v_zetaDeltaFVarIds_1877_);
lean_inc(v_cache_1876_);
lean_inc(v_mctx_1875_);
lean_dec(v___x_1874_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1908_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_depth_1883_; lean_object* v_levelAssignDepth_1884_; lean_object* v_lmvarCounter_1885_; lean_object* v_mvarCounter_1886_; lean_object* v_lDecls_1887_; lean_object* v_decls_1888_; lean_object* v_userNames_1889_; lean_object* v_lAssignment_1890_; lean_object* v_eAssignment_1891_; lean_object* v_dAssignment_1892_; lean_object* v_instanceTypedMVars_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1907_; 
v_depth_1883_ = lean_ctor_get(v_mctx_1875_, 0);
v_levelAssignDepth_1884_ = lean_ctor_get(v_mctx_1875_, 1);
v_lmvarCounter_1885_ = lean_ctor_get(v_mctx_1875_, 2);
v_mvarCounter_1886_ = lean_ctor_get(v_mctx_1875_, 3);
v_lDecls_1887_ = lean_ctor_get(v_mctx_1875_, 4);
v_decls_1888_ = lean_ctor_get(v_mctx_1875_, 5);
v_userNames_1889_ = lean_ctor_get(v_mctx_1875_, 6);
v_lAssignment_1890_ = lean_ctor_get(v_mctx_1875_, 7);
v_eAssignment_1891_ = lean_ctor_get(v_mctx_1875_, 8);
v_dAssignment_1892_ = lean_ctor_get(v_mctx_1875_, 9);
v_instanceTypedMVars_1893_ = lean_ctor_get(v_mctx_1875_, 10);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_mctx_1875_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1895_ = v_mctx_1875_;
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_instanceTypedMVars_1893_);
lean_inc(v_dAssignment_1892_);
lean_inc(v_eAssignment_1891_);
lean_inc(v_lAssignment_1890_);
lean_inc(v_userNames_1889_);
lean_inc(v_decls_1888_);
lean_inc(v_lDecls_1887_);
lean_inc(v_mvarCounter_1886_);
lean_inc(v_lmvarCounter_1885_);
lean_inc(v_levelAssignDepth_1884_);
lean_inc(v_depth_1883_);
lean_dec(v_mctx_1875_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1891_, v_mvarId_1870_, v_val_1871_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 8, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_depth_1883_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_levelAssignDepth_1884_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_lmvarCounter_1885_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_mvarCounter_1886_);
lean_ctor_set(v_reuseFailAlloc_1906_, 4, v_lDecls_1887_);
lean_ctor_set(v_reuseFailAlloc_1906_, 5, v_decls_1888_);
lean_ctor_set(v_reuseFailAlloc_1906_, 6, v_userNames_1889_);
lean_ctor_set(v_reuseFailAlloc_1906_, 7, v_lAssignment_1890_);
lean_ctor_set(v_reuseFailAlloc_1906_, 8, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 9, v_dAssignment_1892_);
lean_ctor_set(v_reuseFailAlloc_1906_, 10, v_instanceTypedMVars_1893_);
v___x_1899_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1899_);
v___x_1901_ = v___x_1881_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_cache_1876_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_zetaDeltaFVarIds_1877_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_postponed_1878_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v_diag_1879_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_st_ref_put(v___y_1872_, v___x_1901_);
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1909_, lean_object* v_val_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1909_, v_val_1910_, v___y_1911_);
lean_dec(v___y_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc_ref(v_type_1914_);
v___x_1920_ = lean_infer_type(v_type_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_Meta_whnfD(v_a_1921_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1957_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1957_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1957_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
switch(lean_obj_tag(v_a_1923_))
{
case 3:
{
lean_object* v_u_1927_; lean_object* v___x_1929_; 
lean_dec_ref(v_type_1914_);
v_u_1927_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_u_1927_);
lean_dec_ref_known(v_a_1923_, 1);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v_u_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_u_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
case 2:
{
lean_object* v_mvarId_1931_; lean_object* v___x_1932_; 
lean_del_object(v___x_1925_);
v_mvarId_1931_ = lean_ctor_get(v_a_1923_, 0);
lean_inc_n(v_mvarId_1931_, 2);
lean_dec_ref_known(v_a_1923_, 1);
v___x_1932_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1931_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; uint8_t v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v_type_1914_);
v___x_1935_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_n(v_a_1936_, 2);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l_Lean_mkSort(v_a_1936_);
v___x_1938_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1931_, v___x_1937_, v_a_1916_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1946_);
v___x_1940_ = v___x_1938_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v_a_1936_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1936_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_dec(v_mvarId_1931_);
return v___x_1935_;
}
}
else
{
lean_object* v___x_1947_; 
lean_dec(v_mvarId_1931_);
v___x_1947_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1947_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_mvarId_1931_);
lean_dec_ref(v_type_1914_);
v_a_1948_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1932_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1932_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
default: 
{
lean_object* v___x_1956_; 
lean_del_object(v___x_1925_);
lean_dec(v_a_1923_);
v___x_1956_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_type_1914_);
v_a_1958_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1922_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1922_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_type_1914_);
v_a_1966_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1920_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1920_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Meta_getLevel(v_type_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1981_, lean_object* v_val_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1981_, v_val_1982_, v___y_1984_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1989_, lean_object* v_val_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1989_, v_val_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1998_, v_x_1999_, v_x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2002_, lean_object* v_x_2003_, size_t v_x_2004_, size_t v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2003_, v_x_2004_, v_x_2005_, v_x_2006_, v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
size_t v_x_1495__boxed_2015_; size_t v_x_1496__boxed_2016_; lean_object* v_res_2017_; 
v_x_1495__boxed_2015_ = lean_unbox_usize(v_x_2011_);
lean_dec(v_x_2011_);
v_x_1496__boxed_2016_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_res_2017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2009_, v_x_2010_, v_x_1495__boxed_2015_, v_x_1496__boxed_2016_, v_x_2013_, v_x_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2018_, lean_object* v_n_2019_, lean_object* v_k_2020_, lean_object* v_v_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2019_, v_k_2020_, v_v_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2023_, size_t v_depth_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_heq_2027_, lean_object* v_i_2028_, lean_object* v_entries_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2024_, v_keys_2025_, v_vals_2026_, v_i_2028_, v_entries_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_depth_2032_, lean_object* v_keys_2033_, lean_object* v_vals_2034_, lean_object* v_heq_2035_, lean_object* v_i_2036_, lean_object* v_entries_2037_){
_start:
{
size_t v_depth_boxed_2038_; lean_object* v_res_2039_; 
v_depth_boxed_2038_ = lean_unbox_usize(v_depth_2032_);
lean_dec(v_depth_2032_);
v_res_2039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2031_, v_depth_boxed_2038_, v_keys_2033_, v_vals_2034_, v_heq_2035_, v_i_2036_, v_entries_2037_);
lean_dec_ref(v_vals_2034_);
lean_dec_ref(v_keys_2033_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2041_, v_x_2042_, v_x_2043_, v_x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2046_, lean_object* v_b_2047_, lean_object* v_c_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
lean_inc(v___y_2052_);
lean_inc_ref(v___y_2051_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
v___x_2054_ = lean_apply_7(v_k_2046_, v_b_2047_, v_c_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, lean_box(0));
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2055_, lean_object* v_b_2056_, lean_object* v_c_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2055_, v_b_2056_, v_c_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2064_, lean_object* v_k_2065_, uint8_t v_cleanupAnnotations_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___f_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2072_, 0, v_k_2065_);
v___x_2073_ = 0;
v___x_2074_ = lean_box(0);
v___x_2075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2073_, v___x_2074_, v_type_2064_, v___f_2072_, v_cleanupAnnotations_2066_, v___x_2073_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_a_2084_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2075_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2075_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2092_, lean_object* v_k_2093_, lean_object* v_cleanupAnnotations_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2100_; lean_object* v_res_2101_; 
v_cleanupAnnotations_boxed_2100_ = lean_unbox(v_cleanupAnnotations_2094_);
v_res_2101_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2092_, v_k_2093_, v_cleanupAnnotations_boxed_2100_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2102_, lean_object* v_type_2103_, lean_object* v_k_2104_, uint8_t v_cleanupAnnotations_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2103_, v_k_2104_, v_cleanupAnnotations_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_type_2113_, lean_object* v_k_2114_, lean_object* v_cleanupAnnotations_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2121_; lean_object* v_res_2122_; 
v_cleanupAnnotations_boxed_2121_ = lean_unbox(v_cleanupAnnotations_2115_);
v_res_2122_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2112_, v_type_2113_, v_k_2114_, v_cleanupAnnotations_boxed_2121_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2132_ == 0)
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_sub(v_i_2124_, v___x_2133_);
v___x_2135_ = lean_array_uget_borrowed(v_as_2123_, v___x_2134_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2129_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___x_2135_);
v___x_2136_ = lean_infer_type(v___x_2135_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Meta_getLevel(v_a_2137_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = l_Lean_mkLevelIMax_x27(v_a_2139_, v_b_2126_);
v_i_2124_ = v___x_2134_;
v_b_2126_ = v___x_2140_;
goto _start;
}
else
{
lean_dec(v_b_2126_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2138_, 1);
v_i_2124_ = v___x_2134_;
v_b_2126_ = v_a_2142_;
goto _start;
}
else
{
return v___x_2138_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_b_2126_);
v_a_2144_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2136_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2136_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_b_2126_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2153_, lean_object* v_i_2154_, lean_object* v_stop_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
size_t v_i_boxed_2162_; size_t v_stop_boxed_2163_; lean_object* v_res_2164_; 
v_i_boxed_2162_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_stop_boxed_2163_ = lean_unbox_usize(v_stop_2155_);
lean_dec(v_stop_2155_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2153_, v_i_boxed_2162_, v_stop_boxed_2163_, v_b_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_as_2153_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2165_, lean_object* v_e_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___y_2173_; lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_getLevel(v_e_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
v___x_2194_ = lean_array_get_size(v_xs_2165_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_nat_dec_lt(v___x_2195_, v___x_2194_);
if (v___x_2196_ == 0)
{
lean_dec(v_a_2193_);
v___y_2173_ = v___x_2192_;
goto v___jp_2172_;
}
else
{
size_t v___x_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref_known(v___x_2192_, 1);
v___x_2197_ = lean_usize_of_nat(v___x_2194_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2165_, v___x_2197_, v___x_2198_, v_a_2193_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
v___y_2173_ = v___x_2199_;
goto v___jp_2172_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2192_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2192_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
v___jp_2172_:
{
if (lean_obj_tag(v___y_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2183_; 
v_a_2174_ = lean_ctor_get(v___y_2173_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___y_2173_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2176_ = v___y_2173_;
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___y_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2178_ = l_Lean_Level_normalize(v_a_2174_);
lean_dec(v_a_2174_);
v___x_2179_ = l_Lean_mkSort(v___x_2178_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2179_);
v___x_2181_ = v___x_2176_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v___y_2173_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___y_2173_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___y_2173_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___y_2173_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2208_, lean_object* v_e_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2208_, v_e_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec_ref(v_xs_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___f_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; 
v___f_2223_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2224_ = 0;
v___x_2225_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2217_, v___f_2223_, v___x_2224_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2233_, lean_object* v_k_2234_, uint8_t v_cleanupAnnotations_2235_, uint8_t v_preserveNondepLet_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___f_2242_; uint8_t v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___f_2242_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2242_, 0, v_k_2234_);
v___x_2243_ = 1;
v___x_2244_ = 0;
v___x_2245_ = lean_box(0);
v___x_2246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2233_, v___x_2243_, v___x_2243_, v_preserveNondepLet_2236_, v___x_2244_, v___x_2245_, v___f_2242_, v_cleanupAnnotations_2235_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2255_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2246_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2246_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2263_, lean_object* v_k_2264_, lean_object* v_cleanupAnnotations_2265_, lean_object* v_preserveNondepLet_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2272_; uint8_t v_preserveNondepLet_boxed_2273_; lean_object* v_res_2274_; 
v_cleanupAnnotations_boxed_2272_ = lean_unbox(v_cleanupAnnotations_2265_);
v_preserveNondepLet_boxed_2273_ = lean_unbox(v_preserveNondepLet_2266_);
v_res_2274_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2263_, v_k_2264_, v_cleanupAnnotations_boxed_2272_, v_preserveNondepLet_boxed_2273_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2275_, lean_object* v_e_2276_, lean_object* v_k_2277_, uint8_t v_cleanupAnnotations_2278_, uint8_t v_preserveNondepLet_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2276_, v_k_2277_, v_cleanupAnnotations_2278_, v_preserveNondepLet_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_e_2287_, lean_object* v_k_2288_, lean_object* v_cleanupAnnotations_2289_, lean_object* v_preserveNondepLet_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2296_; uint8_t v_preserveNondepLet_boxed_2297_; lean_object* v_res_2298_; 
v_cleanupAnnotations_boxed_2296_ = lean_unbox(v_cleanupAnnotations_2289_);
v_preserveNondepLet_boxed_2297_ = lean_unbox(v_preserveNondepLet_2290_);
v_res_2298_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2286_, v_e_2287_, v_k_2288_, v_cleanupAnnotations_boxed_2296_, v_preserveNondepLet_boxed_2297_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2299_, lean_object* v_e_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
lean_inc(v___y_2304_);
lean_inc_ref(v___y_2303_);
lean_inc(v___y_2302_);
lean_inc_ref(v___y_2301_);
v___x_2306_ = lean_infer_type(v_e_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; uint8_t v___x_2308_; uint8_t v___x_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = 0;
v___x_2309_ = 1;
v___x_2310_ = 1;
v___x_2311_ = l_Lean_Meta_mkForallFVars(v_xs_2299_, v_a_2307_, v___x_2308_, v___x_2309_, v___x_2308_, v___x_2310_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2311_;
}
else
{
return v___x_2306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2312_, lean_object* v_e_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2312_, v_e_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec_ref(v_xs_2312_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___f_2327_; uint8_t v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v___f_2327_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2328_ = 0;
v___x_2329_ = 1;
v___x_2330_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2321_, v___f_2327_, v___x_2328_, v___x_2329_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2337_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2351_ = l_Lean_MessageData_ofName(v_mvarId_2344_);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2354_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2363_, lean_object* v_mvarId_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2371_, lean_object* v_mvarId_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2371_, v_mvarId_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v_mctx_2386_; lean_object* v___x_2387_; 
v___x_2385_ = lean_st_ref_get(v_a_2381_);
v_mctx_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc_ref(v_mctx_2386_);
lean_dec(v___x_2385_);
v___x_2387_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2386_, v_mvarId_2379_);
lean_dec_ref(v_mctx_2386_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
return v___x_2388_;
}
else
{
lean_object* v_val_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_mvarId_2379_);
v_val_2389_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_val_2389_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_type_2393_; lean_object* v___x_2395_; 
v_type_2393_ = lean_ctor_get(v_val_2389_, 2);
lean_inc_ref(v_type_2393_);
lean_dec(v_val_2389_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 0);
lean_ctor_set(v___x_2391_, 0, v_type_2393_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_type_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_lctx_2410_; lean_object* v___x_2411_; 
v_lctx_2410_ = lean_ctor_get(v_a_2406_, 2);
lean_inc(v_fvarId_2405_);
lean_inc_ref(v_lctx_2410_);
v___x_2411_ = lean_local_ctx_find(v_lctx_2410_, v_fvarId_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2405_, v_a_2407_, v_a_2408_);
return v___x_2412_;
}
else
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_fvarId_2405_);
v_val_2413_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2415_ = v___x_2411_;
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v___x_2411_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2421_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = l_Lean_LocalDecl_type(v_val_2413_);
lean_dec(v_val_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set_tag(v___x_2415_, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2417_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec_ref(v_a_2423_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2428_, v_a_2429_, v_a_2431_, v_a_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_instMonadEIO(lean_box(0));
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2444_ = l_StateRefT_x27_instMonad___redArg(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___f_2449_; 
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2449_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2449_, 0, v___x_2448_);
return v___f_2449_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___f_2451_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2451_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2451_, 0, v___x_2450_);
return v___f_2451_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; 
v___f_2452_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2453_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___f_2453_);
lean_ctor_set(v___x_2454_, 1, v___f_2452_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___f_2456_; 
v___x_2455_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2456_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2456_, 0, v___x_2455_);
return v___f_2456_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___f_2458_; 
v___x_2457_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2458_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2458_, 0, v___x_2457_);
return v___f_2458_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v___f_2459_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2460_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___f_2460_);
lean_ctor_set(v___x_2461_, 1, v___f_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2464_, lean_object* v_inferType_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
uint8_t v_cacheInferType_2509_; 
v_cacheInferType_2509_ = lean_ctor_get_uint8(v_a_2466_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2509_ == 0)
{
lean_dec_ref(v_e_2464_);
goto v___jp_2471_;
}
else
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_Expr_hasMVar(v_e_2464_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2464_, v_a_2466_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2610_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2610_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2610_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v_cache_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2605_; 
v___x_2516_ = lean_st_ref_get(v_a_2467_);
v_cache_2517_ = lean_ctor_get(v___x_2516_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2606_ = lean_ctor_get(v___x_2516_, 4);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v___x_2516_, 3);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v___x_2516_, 2);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2609_);
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2605_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_cache_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2605_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v_inferType_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v___x_2564_; 
v_inferType_2521_ = lean_ctor_get(v_cache_2517_, 0);
lean_inc_ref(v_inferType_2521_);
lean_dec_ref(v_cache_2517_);
v___f_2522_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2523_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2512_);
v___x_2564_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2522_, v___x_2523_, v_inferType_2521_, v_a_2512_);
lean_dec_ref(v_inferType_2521_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; lean_object* v_toApplicative_2566_; lean_object* v_toFunctor_2567_; lean_object* v_toSeq_2568_; lean_object* v_toSeqLeft_2569_; lean_object* v_toSeqRight_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___x_2580_; 
lean_del_object(v___x_2514_);
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2566_ = lean_ctor_get(v___x_2565_, 0);
v_toFunctor_2567_ = lean_ctor_get(v_toApplicative_2566_, 0);
v_toSeq_2568_ = lean_ctor_get(v_toApplicative_2566_, 2);
v_toSeqLeft_2569_ = lean_ctor_get(v_toApplicative_2566_, 3);
v_toSeqRight_2570_ = lean_ctor_get(v_toApplicative_2566_, 4);
v___f_2571_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2572_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2567_, 2);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toFunctor_2567_);
v___f_2574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2574_, 0, v_toFunctor_2567_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___f_2573_);
lean_ctor_set(v___x_2575_, 1, v___f_2574_);
lean_inc(v_toSeqRight_2570_);
v___f_2576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2576_, 0, v_toSeqRight_2570_);
lean_inc(v_toSeqLeft_2569_);
v___f_2577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2577_, 0, v_toSeqLeft_2569_);
lean_inc(v_toSeq_2568_);
v___f_2578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2578_, 0, v_toSeq_2568_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 4, v___f_2576_);
lean_ctor_set(v___x_2519_, 3, v___f_2577_);
lean_ctor_set(v___x_2519_, 2, v___f_2578_);
lean_ctor_set(v___x_2519_, 1, v___f_2571_);
lean_ctor_set(v___x_2519_, 0, v___x_2575_);
v___x_2580_ = v___x_2519_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___f_2571_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v___f_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v___f_2577_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v___f_2576_);
v___x_2580_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v_cancelTk_x3f_2587_; 
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___f_2572_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2583_ = l_Lean_Core_instMonadRefCoreM;
v___x_2584_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2585_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2584_, v___x_2581_);
v___x_2586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2582_);
lean_ctor_set(v___x_2586_, 1, v___x_2583_);
lean_ctor_set(v___x_2586_, 2, v___x_2585_);
v_cancelTk_x3f_2587_ = lean_ctor_get(v_a_2468_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2587_) == 1)
{
lean_object* v_val_2588_; uint8_t v___x_2589_; 
v_val_2588_ = lean_ctor_get(v_cancelTk_x3f_2587_, 0);
v___x_2589_ = l_IO_CancelToken_isSet(v_val_2588_);
if (v___x_2589_ == 0)
{
lean_dec_ref_known(v___x_2586_, 3);
goto v___jp_2524_;
}
else
{
lean_object* v___x_1979__overap_2590_; lean_object* v___x_2591_; 
v___x_1979__overap_2590_ = l_Lean_throwInterruptException___redArg(v___x_2586_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2591_ = lean_apply_3(v___x_1979__overap_2590_, v_a_2468_, v_a_2469_, lean_box(0));
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
goto v___jp_2524_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2512_);
lean_dec_ref(v_inferType_2465_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2586_, 3);
goto v___jp_2524_;
}
}
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2603_; 
lean_del_object(v___x_2519_);
lean_dec(v_a_2512_);
lean_dec_ref(v_inferType_2465_);
v_val_2601_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v___x_2564_, 1);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v_val_2601_);
v___x_2603_ = v___x_2514_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_val_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
v___jp_2524_:
{
lean_object* v___x_2525_; 
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2525_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
v___x_2527_ = l_Lean_Expr_hasMVar(v_a_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2525_, 0);
lean_dec(v_unused_2563_);
v___x_2529_ = v___x_2525_;
v_isShared_2530_ = v_isSharedCheck_2562_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v___x_2525_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2562_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v_cache_2532_; lean_object* v_mctx_2533_; lean_object* v_zetaDeltaFVarIds_2534_; lean_object* v_postponed_2535_; lean_object* v_diag_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2561_; 
v___x_2531_ = lean_st_ref_take(v_a_2467_);
v_cache_2532_ = lean_ctor_get(v___x_2531_, 1);
v_mctx_2533_ = lean_ctor_get(v___x_2531_, 0);
v_zetaDeltaFVarIds_2534_ = lean_ctor_get(v___x_2531_, 2);
v_postponed_2535_ = lean_ctor_get(v___x_2531_, 3);
v_diag_2536_ = lean_ctor_get(v___x_2531_, 4);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2538_ = v___x_2531_;
v_isShared_2539_ = v_isSharedCheck_2561_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_diag_2536_);
lean_inc(v_postponed_2535_);
lean_inc(v_zetaDeltaFVarIds_2534_);
lean_inc(v_cache_2532_);
lean_inc(v_mctx_2533_);
lean_dec(v___x_2531_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2561_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_inferType_2540_; lean_object* v_funInfo_2541_; lean_object* v_synthInstance_2542_; lean_object* v_whnf_2543_; lean_object* v_defEqTrans_2544_; lean_object* v_defEqPerm_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2560_; 
v_inferType_2540_ = lean_ctor_get(v_cache_2532_, 0);
v_funInfo_2541_ = lean_ctor_get(v_cache_2532_, 1);
v_synthInstance_2542_ = lean_ctor_get(v_cache_2532_, 2);
v_whnf_2543_ = lean_ctor_get(v_cache_2532_, 3);
v_defEqTrans_2544_ = lean_ctor_get(v_cache_2532_, 4);
v_defEqPerm_2545_ = lean_ctor_get(v_cache_2532_, 5);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_cache_2532_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2547_ = v_cache_2532_;
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_defEqPerm_2545_);
lean_inc(v_defEqTrans_2544_);
lean_inc(v_whnf_2543_);
lean_inc(v_synthInstance_2542_);
lean_inc(v_funInfo_2541_);
lean_inc(v_inferType_2540_);
lean_dec(v_cache_2532_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_inc(v_a_2526_);
v___x_2549_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2522_, v___x_2523_, v_inferType_2540_, v_a_2512_, v_a_2526_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2549_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_funInfo_2541_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_synthInstance_2542_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_whnf_2543_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_defEqTrans_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 5, v_defEqPerm_2545_);
v___x_2551_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2551_);
v___x_2553_ = v___x_2538_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_mctx_2533_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_zetaDeltaFVarIds_2534_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_postponed_2535_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_diag_2536_);
v___x_2553_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_st_ref_put(v_a_2467_, v___x_2553_);
if (v_isShared_2530_ == 0)
{
v___x_2556_ = v___x_2529_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2526_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2526_);
lean_dec(v_a_2512_);
return v___x_2525_;
}
}
else
{
lean_dec(v_a_2512_);
return v___x_2525_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref(v_inferType_2465_);
v_a_2611_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2511_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2511_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_dec_ref(v_e_2464_);
goto v___jp_2471_;
}
}
v___jp_2471_:
{
lean_object* v___x_2472_; lean_object* v_toApplicative_2473_; lean_object* v_toFunctor_2474_; lean_object* v_toSeq_2475_; lean_object* v_toSeqLeft_2476_; lean_object* v_toSeqRight_2477_; lean_object* v___f_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_cancelTk_x3f_2493_; 
v___x_2472_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2473_ = lean_ctor_get(v___x_2472_, 0);
v_toFunctor_2474_ = lean_ctor_get(v_toApplicative_2473_, 0);
v_toSeq_2475_ = lean_ctor_get(v_toApplicative_2473_, 2);
v_toSeqLeft_2476_ = lean_ctor_get(v_toApplicative_2473_, 3);
v_toSeqRight_2477_ = lean_ctor_get(v_toApplicative_2473_, 4);
v___f_2478_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2479_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2474_, 2);
v___f_2480_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2480_, 0, v_toFunctor_2474_);
v___f_2481_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2481_, 0, v_toFunctor_2474_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___f_2480_);
lean_ctor_set(v___x_2482_, 1, v___f_2481_);
lean_inc(v_toSeqRight_2477_);
v___f_2483_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2483_, 0, v_toSeqRight_2477_);
lean_inc(v_toSeqLeft_2476_);
v___f_2484_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2484_, 0, v_toSeqLeft_2476_);
lean_inc(v_toSeq_2475_);
v___f_2485_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2485_, 0, v_toSeq_2475_);
v___x_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2482_);
lean_ctor_set(v___x_2486_, 1, v___f_2478_);
lean_ctor_set(v___x_2486_, 2, v___f_2485_);
lean_ctor_set(v___x_2486_, 3, v___f_2484_);
lean_ctor_set(v___x_2486_, 4, v___f_2483_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___f_2479_);
v___x_2488_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2489_ = l_Lean_Core_instMonadRefCoreM;
v___x_2490_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2491_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2490_, v___x_2487_);
v___x_2492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2488_);
lean_ctor_set(v___x_2492_, 1, v___x_2489_);
lean_ctor_set(v___x_2492_, 2, v___x_2491_);
v_cancelTk_x3f_2493_ = lean_ctor_get(v_a_2468_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2493_) == 1)
{
lean_object* v_val_2494_; uint8_t v___x_2495_; 
v_val_2494_ = lean_ctor_get(v_cancelTk_x3f_2493_, 0);
v___x_2495_ = l_IO_CancelToken_isSet(v_val_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2492_, 3);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2496_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2496_;
}
else
{
lean_object* v___x_1694__overap_2497_; lean_object* v___x_2498_; 
v___x_1694__overap_2497_ = l_Lean_throwInterruptException___redArg(v___x_2492_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2498_ = lean_apply_3(v___x_1694__overap_2497_, v_a_2468_, v_a_2469_, lean_box(0));
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2498_, 1);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2499_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2499_;
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref(v_inferType_2465_);
v_a_2500_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2498_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
else
{
lean_object* v___x_2508_; 
lean_dec_ref_known(v___x_2492_, 3);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2508_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2619_, lean_object* v_inferType_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2619_, v_inferType_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
return v_res_2626_;
}
}
static lean_object* _init_l_Lean_Meta_withInferTypeConfig___redArg___closed__0(void){
_start:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = 2;
v___x_2628_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___y_2636_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; uint8_t v___y_2644_; uint8_t v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2676_; lean_object* v___x_2704_; uint8_t v_transparency_2705_; uint8_t v___x_2706_; uint8_t v___x_2707_; 
v___x_2704_ = l_Lean_Meta_Context_config(v_a_2630_);
v_transparency_2705_ = lean_ctor_get_uint8(v___x_2704_, 9);
lean_dec_ref(v___x_2704_);
v___x_2706_ = 1;
v___x_2707_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
v___y_2676_ = v_transparency_2705_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v___x_2706_;
goto v___jp_2675_;
}
v___jp_2635_:
{
lean_object* v___x_2647_; uint8_t v_foApprox_2648_; uint8_t v_ctxApprox_2649_; uint8_t v_quasiPatternApprox_2650_; uint8_t v_constApprox_2651_; uint8_t v_isDefEqStuckEx_2652_; uint8_t v_unificationHints_2653_; uint8_t v_proofIrrelevance_2654_; uint8_t v_assignSyntheticOpaque_2655_; uint8_t v_offsetCnstrs_2656_; uint8_t v_transparency_2657_; uint8_t v_univApprox_2658_; uint8_t v_zetaUnused_2659_; uint8_t v_canUnfoldPredicateConfig_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2674_; 
v___x_2647_ = l_Lean_Meta_Context_config(v___y_2640_);
lean_dec_ref(v___y_2640_);
v_foApprox_2648_ = lean_ctor_get_uint8(v___x_2647_, 0);
v_ctxApprox_2649_ = lean_ctor_get_uint8(v___x_2647_, 1);
v_quasiPatternApprox_2650_ = lean_ctor_get_uint8(v___x_2647_, 2);
v_constApprox_2651_ = lean_ctor_get_uint8(v___x_2647_, 3);
v_isDefEqStuckEx_2652_ = lean_ctor_get_uint8(v___x_2647_, 4);
v_unificationHints_2653_ = lean_ctor_get_uint8(v___x_2647_, 5);
v_proofIrrelevance_2654_ = lean_ctor_get_uint8(v___x_2647_, 6);
v_assignSyntheticOpaque_2655_ = lean_ctor_get_uint8(v___x_2647_, 7);
v_offsetCnstrs_2656_ = lean_ctor_get_uint8(v___x_2647_, 8);
v_transparency_2657_ = lean_ctor_get_uint8(v___x_2647_, 9);
v_univApprox_2658_ = lean_ctor_get_uint8(v___x_2647_, 11);
v_zetaUnused_2659_ = lean_ctor_get_uint8(v___x_2647_, 17);
v_canUnfoldPredicateConfig_2660_ = lean_ctor_get_uint8(v___x_2647_, 19);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2662_ = v___x_2647_;
v_isShared_2663_ = v_isSharedCheck_2674_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2647_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2674_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___x_2664_; uint8_t v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2668_; 
v___x_2664_ = 1;
v___x_2665_ = 0;
v___x_2666_ = 2;
if (v_isShared_2663_ == 0)
{
v___x_2668_ = v___x_2662_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 0, v_foApprox_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 1, v_ctxApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 2, v_quasiPatternApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 3, v_constApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 4, v_isDefEqStuckEx_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 5, v_unificationHints_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 6, v_proofIrrelevance_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 7, v_assignSyntheticOpaque_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 8, v_offsetCnstrs_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 9, v_transparency_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 11, v_univApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 17, v_zetaUnused_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 19, v_canUnfoldPredicateConfig_2660_);
v___x_2668_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
uint64_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_ctor_set_uint8(v___x_2668_, 10, v___x_2665_);
lean_ctor_set_uint8(v___x_2668_, 12, v___x_2664_);
lean_ctor_set_uint8(v___x_2668_, 13, v___x_2664_);
lean_ctor_set_uint8(v___x_2668_, 14, v___x_2666_);
lean_ctor_set_uint8(v___x_2668_, 15, v___x_2664_);
lean_ctor_set_uint8(v___x_2668_, 16, v___x_2664_);
lean_ctor_set_uint8(v___x_2668_, 18, v___x_2664_);
v___x_2669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set_uint64(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_inc(v___y_2638_);
lean_inc(v___y_2646_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2641_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2639_);
v___x_2671_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___y_2639_);
lean_ctor_set(v___x_2671_, 2, v___y_2636_);
lean_ctor_set(v___x_2671_, 3, v___y_2641_);
lean_ctor_set(v___x_2671_, 4, v___y_2643_);
lean_ctor_set(v___x_2671_, 5, v___y_2646_);
lean_ctor_set(v___x_2671_, 6, v___y_2638_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7, v___y_2644_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 1, v___y_2637_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 2, v___y_2645_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 3, v___y_2642_);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
v___x_2672_ = lean_apply_5(v_x_2629_, v___x_2671_, v_a_2631_, v_a_2632_, v_a_2633_, lean_box(0));
return v___x_2672_;
}
}
}
v___jp_2675_:
{
lean_object* v_keyedConfig_2677_; uint8_t v_trackZetaDelta_2678_; lean_object* v_zetaDeltaSet_2679_; lean_object* v_lctx_2680_; lean_object* v_localInstances_2681_; lean_object* v_defEqCtx_x3f_2682_; lean_object* v_synthPendingDepth_2683_; lean_object* v_customCanUnfoldPredicate_x3f_2684_; uint8_t v_univApprox_2685_; uint8_t v_inTypeClassResolution_2686_; uint8_t v_cacheInferType_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v_beta_2691_; 
v_keyedConfig_2677_ = lean_ctor_get(v_a_2630_, 0);
v_trackZetaDelta_2678_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7);
v_zetaDeltaSet_2679_ = lean_ctor_get(v_a_2630_, 1);
v_lctx_2680_ = lean_ctor_get(v_a_2630_, 2);
v_localInstances_2681_ = lean_ctor_get(v_a_2630_, 3);
v_defEqCtx_x3f_2682_ = lean_ctor_get(v_a_2630_, 4);
v_synthPendingDepth_2683_ = lean_ctor_get(v_a_2630_, 5);
v_customCanUnfoldPredicate_x3f_2684_ = lean_ctor_get(v_a_2630_, 6);
v_univApprox_2685_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2686_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 2);
v_cacheInferType_2687_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2677_);
v___x_2688_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2676_, v_keyedConfig_2677_);
lean_inc(v_customCanUnfoldPredicate_x3f_2684_);
lean_inc(v_synthPendingDepth_2683_);
lean_inc(v_defEqCtx_x3f_2682_);
lean_inc_ref(v_localInstances_2681_);
lean_inc_ref(v_lctx_2680_);
lean_inc(v_zetaDeltaSet_2679_);
v___x_2689_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
lean_ctor_set(v___x_2689_, 1, v_zetaDeltaSet_2679_);
lean_ctor_set(v___x_2689_, 2, v_lctx_2680_);
lean_ctor_set(v___x_2689_, 3, v_localInstances_2681_);
lean_ctor_set(v___x_2689_, 4, v_defEqCtx_x3f_2682_);
lean_ctor_set(v___x_2689_, 5, v_synthPendingDepth_2683_);
lean_ctor_set(v___x_2689_, 6, v_customCanUnfoldPredicate_x3f_2684_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7, v_trackZetaDelta_2678_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 1, v_univApprox_2685_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2686_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 3, v_cacheInferType_2687_);
v___x_2690_ = l_Lean_Meta_Context_config(v___x_2689_);
v_beta_2691_ = lean_ctor_get_uint8(v___x_2690_, 13);
if (v_beta_2691_ == 0)
{
lean_dec_ref(v___x_2690_);
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v_iota_2692_; 
v_iota_2692_ = lean_ctor_get_uint8(v___x_2690_, 12);
if (v_iota_2692_ == 0)
{
lean_dec_ref(v___x_2690_);
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v_zeta_2693_; 
v_zeta_2693_ = lean_ctor_get_uint8(v___x_2690_, 15);
if (v_zeta_2693_ == 0)
{
lean_dec_ref(v___x_2690_);
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v_zetaHave_2694_; 
v_zetaHave_2694_ = lean_ctor_get_uint8(v___x_2690_, 18);
if (v_zetaHave_2694_ == 0)
{
lean_dec_ref(v___x_2690_);
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v_zetaDelta_2695_; 
v_zetaDelta_2695_ = lean_ctor_get_uint8(v___x_2690_, 16);
if (v_zetaDelta_2695_ == 0)
{
lean_dec_ref(v___x_2690_);
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v_etaStruct_2696_; uint8_t v_proj_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_etaStruct_2696_ = lean_ctor_get_uint8(v___x_2690_, 10);
v_proj_2697_ = lean_ctor_get_uint8(v___x_2690_, 14);
lean_dec_ref(v___x_2690_);
v___x_2698_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2697_);
v___x_2699_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___closed__0);
v___x_2700_ = lean_nat_dec_eq(v___x_2698_, v___x_2699_);
lean_dec(v___x_2698_);
if (v___x_2700_ == 0)
{
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
uint8_t v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = 0;
v___x_2702_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2696_, v___x_2701_);
if (v___x_2702_ == 0)
{
v___y_2636_ = v_lctx_2680_;
v___y_2637_ = v_univApprox_2685_;
v___y_2638_ = v_customCanUnfoldPredicate_x3f_2684_;
v___y_2639_ = v_zetaDeltaSet_2679_;
v___y_2640_ = v___x_2689_;
v___y_2641_ = v_localInstances_2681_;
v___y_2642_ = v_cacheInferType_2687_;
v___y_2643_ = v_defEqCtx_x3f_2682_;
v___y_2644_ = v_trackZetaDelta_2678_;
v___y_2645_ = v_inTypeClassResolution_2686_;
v___y_2646_ = v_synthPendingDepth_2683_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2703_; 
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
v___x_2703_ = lean_apply_5(v_x_2629_, v___x_2689_, v_a_2631_, v_a_2632_, v_a_2633_, lean_box(0));
return v___x_2703_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2715_, lean_object* v_x_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___y_2723_; uint8_t v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; uint8_t v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; uint8_t v___y_2732_; lean_object* v___y_2733_; uint8_t v___y_2763_; lean_object* v___x_2791_; uint8_t v_transparency_2792_; uint8_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2791_ = l_Lean_Meta_Context_config(v_a_2717_);
v_transparency_2792_ = lean_ctor_get_uint8(v___x_2791_, 9);
lean_dec_ref(v___x_2791_);
v___x_2793_ = 1;
v___x_2794_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2792_, v___x_2793_);
if (v___x_2794_ == 0)
{
v___y_2763_ = v_transparency_2792_;
goto v___jp_2762_;
}
else
{
v___y_2763_ = v___x_2793_;
goto v___jp_2762_;
}
v___jp_2722_:
{
lean_object* v___x_2734_; uint8_t v_foApprox_2735_; uint8_t v_ctxApprox_2736_; uint8_t v_quasiPatternApprox_2737_; uint8_t v_constApprox_2738_; uint8_t v_isDefEqStuckEx_2739_; uint8_t v_unificationHints_2740_; uint8_t v_proofIrrelevance_2741_; uint8_t v_assignSyntheticOpaque_2742_; uint8_t v_offsetCnstrs_2743_; uint8_t v_transparency_2744_; uint8_t v_univApprox_2745_; uint8_t v_zetaUnused_2746_; uint8_t v_canUnfoldPredicateConfig_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2761_; 
v___x_2734_ = l_Lean_Meta_Context_config(v___y_2727_);
lean_dec_ref(v___y_2727_);
v_foApprox_2735_ = lean_ctor_get_uint8(v___x_2734_, 0);
v_ctxApprox_2736_ = lean_ctor_get_uint8(v___x_2734_, 1);
v_quasiPatternApprox_2737_ = lean_ctor_get_uint8(v___x_2734_, 2);
v_constApprox_2738_ = lean_ctor_get_uint8(v___x_2734_, 3);
v_isDefEqStuckEx_2739_ = lean_ctor_get_uint8(v___x_2734_, 4);
v_unificationHints_2740_ = lean_ctor_get_uint8(v___x_2734_, 5);
v_proofIrrelevance_2741_ = lean_ctor_get_uint8(v___x_2734_, 6);
v_assignSyntheticOpaque_2742_ = lean_ctor_get_uint8(v___x_2734_, 7);
v_offsetCnstrs_2743_ = lean_ctor_get_uint8(v___x_2734_, 8);
v_transparency_2744_ = lean_ctor_get_uint8(v___x_2734_, 9);
v_univApprox_2745_ = lean_ctor_get_uint8(v___x_2734_, 11);
v_zetaUnused_2746_ = lean_ctor_get_uint8(v___x_2734_, 17);
v_canUnfoldPredicateConfig_2747_ = lean_ctor_get_uint8(v___x_2734_, 19);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2749_ = v___x_2734_;
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
else
{
lean_dec(v___x_2734_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint8_t v___x_2751_; uint8_t v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2755_; 
v___x_2751_ = 1;
v___x_2752_ = 0;
v___x_2753_ = 2;
if (v_isShared_2750_ == 0)
{
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 0, v_foApprox_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 1, v_ctxApprox_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 2, v_quasiPatternApprox_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 3, v_constApprox_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 4, v_isDefEqStuckEx_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 5, v_unificationHints_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 6, v_proofIrrelevance_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 7, v_assignSyntheticOpaque_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 8, v_offsetCnstrs_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 9, v_transparency_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 11, v_univApprox_2745_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 17, v_zetaUnused_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, 19, v_canUnfoldPredicateConfig_2747_);
v___x_2755_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
uint64_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_ctor_set_uint8(v___x_2755_, 10, v___x_2752_);
lean_ctor_set_uint8(v___x_2755_, 12, v___x_2751_);
lean_ctor_set_uint8(v___x_2755_, 13, v___x_2751_);
lean_ctor_set_uint8(v___x_2755_, 14, v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, 15, v___x_2751_);
lean_ctor_set_uint8(v___x_2755_, 16, v___x_2751_);
lean_ctor_set_uint8(v___x_2755_, 18, v___x_2751_);
v___x_2756_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set_uint64(v___x_2757_, sizeof(void*)*1, v___x_2756_);
lean_inc(v___y_2725_);
lean_inc(v___y_2733_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2728_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2726_);
v___x_2758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___y_2726_);
lean_ctor_set(v___x_2758_, 2, v___y_2723_);
lean_ctor_set(v___x_2758_, 3, v___y_2728_);
lean_ctor_set(v___x_2758_, 4, v___y_2730_);
lean_ctor_set(v___x_2758_, 5, v___y_2733_);
lean_ctor_set(v___x_2758_, 6, v___y_2725_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7, v___y_2731_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 1, v___y_2724_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 2, v___y_2732_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 3, v___y_2729_);
lean_inc(v_a_2720_);
lean_inc_ref(v_a_2719_);
lean_inc(v_a_2718_);
v___x_2759_ = lean_apply_5(v_x_2716_, v___x_2758_, v_a_2718_, v_a_2719_, v_a_2720_, lean_box(0));
return v___x_2759_;
}
}
}
v___jp_2762_:
{
lean_object* v_keyedConfig_2764_; uint8_t v_trackZetaDelta_2765_; lean_object* v_zetaDeltaSet_2766_; lean_object* v_lctx_2767_; lean_object* v_localInstances_2768_; lean_object* v_defEqCtx_x3f_2769_; lean_object* v_synthPendingDepth_2770_; lean_object* v_customCanUnfoldPredicate_x3f_2771_; uint8_t v_univApprox_2772_; uint8_t v_inTypeClassResolution_2773_; uint8_t v_cacheInferType_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v_beta_2778_; 
v_keyedConfig_2764_ = lean_ctor_get(v_a_2717_, 0);
v_trackZetaDelta_2765_ = lean_ctor_get_uint8(v_a_2717_, sizeof(void*)*7);
v_zetaDeltaSet_2766_ = lean_ctor_get(v_a_2717_, 1);
v_lctx_2767_ = lean_ctor_get(v_a_2717_, 2);
v_localInstances_2768_ = lean_ctor_get(v_a_2717_, 3);
v_defEqCtx_x3f_2769_ = lean_ctor_get(v_a_2717_, 4);
v_synthPendingDepth_2770_ = lean_ctor_get(v_a_2717_, 5);
v_customCanUnfoldPredicate_x3f_2771_ = lean_ctor_get(v_a_2717_, 6);
v_univApprox_2772_ = lean_ctor_get_uint8(v_a_2717_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2773_ = lean_ctor_get_uint8(v_a_2717_, sizeof(void*)*7 + 2);
v_cacheInferType_2774_ = lean_ctor_get_uint8(v_a_2717_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2764_);
v___x_2775_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2763_, v_keyedConfig_2764_);
lean_inc(v_customCanUnfoldPredicate_x3f_2771_);
lean_inc(v_synthPendingDepth_2770_);
lean_inc(v_defEqCtx_x3f_2769_);
lean_inc_ref(v_localInstances_2768_);
lean_inc_ref(v_lctx_2767_);
lean_inc(v_zetaDeltaSet_2766_);
v___x_2776_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v_zetaDeltaSet_2766_);
lean_ctor_set(v___x_2776_, 2, v_lctx_2767_);
lean_ctor_set(v___x_2776_, 3, v_localInstances_2768_);
lean_ctor_set(v___x_2776_, 4, v_defEqCtx_x3f_2769_);
lean_ctor_set(v___x_2776_, 5, v_synthPendingDepth_2770_);
lean_ctor_set(v___x_2776_, 6, v_customCanUnfoldPredicate_x3f_2771_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7, v_trackZetaDelta_2765_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 1, v_univApprox_2772_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2773_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 3, v_cacheInferType_2774_);
v___x_2777_ = l_Lean_Meta_Context_config(v___x_2776_);
v_beta_2778_ = lean_ctor_get_uint8(v___x_2777_, 13);
if (v_beta_2778_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v_iota_2779_; 
v_iota_2779_ = lean_ctor_get_uint8(v___x_2777_, 12);
if (v_iota_2779_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v_zeta_2780_; 
v_zeta_2780_ = lean_ctor_get_uint8(v___x_2777_, 15);
if (v_zeta_2780_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v_zetaHave_2781_; 
v_zetaHave_2781_ = lean_ctor_get_uint8(v___x_2777_, 18);
if (v_zetaHave_2781_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v_zetaDelta_2782_; 
v_zetaDelta_2782_ = lean_ctor_get_uint8(v___x_2777_, 16);
if (v_zetaDelta_2782_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v_etaStruct_2783_; uint8_t v_proj_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_etaStruct_2783_ = lean_ctor_get_uint8(v___x_2777_, 10);
v_proj_2784_ = lean_ctor_get_uint8(v___x_2777_, 14);
lean_dec_ref(v___x_2777_);
v___x_2785_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2784_);
v___x_2786_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___closed__0);
v___x_2787_ = lean_nat_dec_eq(v___x_2785_, v___x_2786_);
lean_dec(v___x_2785_);
if (v___x_2787_ == 0)
{
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
uint8_t v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = 0;
v___x_2789_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2783_, v___x_2788_);
if (v___x_2789_ == 0)
{
v___y_2723_ = v_lctx_2767_;
v___y_2724_ = v_univApprox_2772_;
v___y_2725_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2726_ = v_zetaDeltaSet_2766_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_localInstances_2768_;
v___y_2729_ = v_cacheInferType_2774_;
v___y_2730_ = v_defEqCtx_x3f_2769_;
v___y_2731_ = v_trackZetaDelta_2765_;
v___y_2732_ = v_inTypeClassResolution_2773_;
v___y_2733_ = v_synthPendingDepth_2770_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2790_; 
lean_inc(v_a_2720_);
lean_inc_ref(v_a_2719_);
lean_inc(v_a_2718_);
v___x_2790_ = lean_apply_5(v_x_2716_, v___x_2776_, v_a_2718_, v_a_2719_, v_a_2720_, lean_box(0));
return v___x_2790_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2795_, lean_object* v_x_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2795_, v_x_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lean_interruptExceptionId;
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v___x_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
lean_object* v_ks_2825_; lean_object* v_vs_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2855_; 
v_ks_2825_ = lean_ctor_get(v_x_2821_, 0);
v_vs_2826_ = lean_ctor_get(v_x_2821_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_x_2821_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2828_ = v_x_2821_;
v_isShared_2829_ = v_isSharedCheck_2855_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_vs_2826_);
lean_inc(v_ks_2825_);
lean_dec(v_x_2821_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2855_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
uint8_t v___y_2831_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = lean_array_get_size(v_ks_2825_);
v___x_2844_ = lean_nat_dec_lt(v_x_2822_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2828_);
lean_dec(v_x_2822_);
v___x_2845_ = lean_array_push(v_ks_2825_, v_x_2823_);
v___x_2846_ = lean_array_push(v_vs_2826_, v_x_2824_);
v___x_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
return v___x_2847_;
}
else
{
lean_object* v_expr_2848_; uint64_t v_configKey_2849_; lean_object* v_k_x27_2850_; lean_object* v_expr_2851_; uint64_t v_configKey_2852_; uint8_t v___x_2853_; 
v_expr_2848_ = lean_ctor_get(v_x_2823_, 0);
v_configKey_2849_ = lean_ctor_get_uint64(v_x_2823_, sizeof(void*)*1);
v_k_x27_2850_ = lean_array_fget_borrowed(v_ks_2825_, v_x_2822_);
v_expr_2851_ = lean_ctor_get(v_k_x27_2850_, 0);
v_configKey_2852_ = lean_ctor_get_uint64(v_k_x27_2850_, sizeof(void*)*1);
v___x_2853_ = lean_expr_equal(v_expr_2848_, v_expr_2851_);
if (v___x_2853_ == 0)
{
v___y_2831_ = v___x_2853_;
goto v___jp_2830_;
}
else
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_uint64_dec_eq(v_configKey_2849_, v_configKey_2852_);
v___y_2831_ = v___x_2854_;
goto v___jp_2830_;
}
}
v___jp_2830_:
{
if (v___y_2831_ == 0)
{
lean_object* v___x_2833_; 
if (v_isShared_2829_ == 0)
{
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_ks_2825_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_vs_2826_);
v___x_2833_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_unsigned_to_nat(1u);
v___x_2835_ = lean_nat_add(v_x_2822_, v___x_2834_);
lean_dec(v_x_2822_);
v_x_2821_ = v___x_2833_;
v_x_2822_ = v___x_2835_;
goto _start;
}
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = lean_array_fset(v_ks_2825_, v_x_2822_, v_x_2823_);
v___x_2839_ = lean_array_fset(v_vs_2826_, v_x_2822_, v_x_2824_);
lean_dec(v_x_2822_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v___x_2839_);
lean_ctor_set(v___x_2828_, 0, v___x_2838_);
v___x_2841_ = v___x_2828_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2856_, lean_object* v_k_2857_, lean_object* v_v_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2856_, v___x_2859_, v_k_2857_, v_v_2858_);
return v___x_2860_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2862_, size_t v_x_2863_, size_t v_x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2862_) == 0)
{
lean_object* v_es_2867_; size_t v___x_2868_; size_t v___x_2869_; lean_object* v_j_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_es_2867_ = lean_ctor_get(v_x_2862_, 0);
v___x_2868_ = ((size_t)31ULL);
v___x_2869_ = lean_usize_land(v_x_2863_, v___x_2868_);
v_j_2870_ = lean_usize_to_nat(v___x_2869_);
v___x_2871_ = lean_array_get_size(v_es_2867_);
v___x_2872_ = lean_nat_dec_lt(v_j_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_dec(v_j_2870_);
lean_dec(v_x_2866_);
lean_dec_ref(v_x_2865_);
return v_x_2862_;
}
else
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2918_; 
lean_inc_ref(v_es_2867_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v_x_2862_, 0);
lean_dec(v_unused_2919_);
v___x_2874_ = v_x_2862_;
v_isShared_2875_ = v_isSharedCheck_2918_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v_x_2862_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2918_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_v_2876_; lean_object* v___x_2877_; lean_object* v_xs_x27_2878_; lean_object* v___y_2880_; 
v_v_2876_ = lean_array_fget(v_es_2867_, v_j_2870_);
v___x_2877_ = lean_box(0);
v_xs_x27_2878_ = lean_array_fset(v_es_2867_, v_j_2870_, v___x_2877_);
switch(lean_obj_tag(v_v_2876_))
{
case 0:
{
lean_object* v_key_2885_; lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2903_; 
v_key_2885_ = lean_ctor_get(v_v_2876_, 0);
v_val_2886_ = lean_ctor_get(v_v_2876_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_v_2876_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2888_ = v_v_2876_;
v_isShared_2889_ = v_isSharedCheck_2903_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_inc(v_key_2885_);
lean_dec(v_v_2876_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2903_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint8_t v___y_2891_; lean_object* v_expr_2897_; uint64_t v_configKey_2898_; lean_object* v_expr_2899_; uint64_t v_configKey_2900_; uint8_t v___x_2901_; 
v_expr_2897_ = lean_ctor_get(v_x_2865_, 0);
v_configKey_2898_ = lean_ctor_get_uint64(v_x_2865_, sizeof(void*)*1);
v_expr_2899_ = lean_ctor_get(v_key_2885_, 0);
v_configKey_2900_ = lean_ctor_get_uint64(v_key_2885_, sizeof(void*)*1);
v___x_2901_ = lean_expr_equal(v_expr_2897_, v_expr_2899_);
if (v___x_2901_ == 0)
{
v___y_2891_ = v___x_2901_;
goto v___jp_2890_;
}
else
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_uint64_dec_eq(v_configKey_2898_, v_configKey_2900_);
v___y_2891_ = v___x_2902_;
goto v___jp_2890_;
}
v___jp_2890_:
{
if (v___y_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2888_);
v___x_2892_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2885_, v_val_2886_, v_x_2865_, v_x_2866_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___y_2880_ = v___x_2893_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2895_; 
lean_dec(v_val_2886_);
lean_dec(v_key_2885_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v_x_2866_);
lean_ctor_set(v___x_2888_, 0, v_x_2865_);
v___x_2895_ = v___x_2888_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_x_2865_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_x_2866_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
v___y_2880_ = v___x_2895_;
goto v___jp_2879_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2916_; 
v_node_2904_ = lean_ctor_get(v_v_2876_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_v_2876_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2906_ = v_v_2876_;
v_isShared_2907_ = v_isSharedCheck_2916_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_node_2904_);
lean_dec(v_v_2876_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2916_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
size_t v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2908_ = ((size_t)5ULL);
v___x_2909_ = lean_usize_shift_right(v_x_2863_, v___x_2908_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_x_2864_, v___x_2910_);
v___x_2912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2904_, v___x_2909_, v___x_2911_, v_x_2865_, v_x_2866_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2912_);
v___x_2914_ = v___x_2906_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
v___y_2880_ = v___x_2914_;
goto v___jp_2879_;
}
}
}
default: 
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v_x_2865_);
lean_ctor_set(v___x_2917_, 1, v_x_2866_);
v___y_2880_ = v___x_2917_;
goto v___jp_2879_;
}
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_array_fset(v_xs_x27_2878_, v_j_2870_, v___y_2880_);
lean_dec(v_j_2870_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2881_);
v___x_2883_ = v___x_2874_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v_ks_2920_; lean_object* v_vs_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2939_; 
v_ks_2920_ = lean_ctor_get(v_x_2862_, 0);
v_vs_2921_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2923_ = v_x_2862_;
v_isShared_2924_ = v_isSharedCheck_2939_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_vs_2921_);
lean_inc(v_ks_2920_);
lean_dec(v_x_2862_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2939_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_ks_2920_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_vs_2921_);
v___x_2926_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v_newNode_2927_; size_t v___x_2928_; uint8_t v___x_2929_; 
v_newNode_2927_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2926_, v_x_2865_, v_x_2866_);
v___x_2928_ = ((size_t)7ULL);
v___x_2929_ = lean_usize_dec_le(v___x_2928_, v_x_2864_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2927_);
v___x_2931_ = lean_unsigned_to_nat(4u);
v___x_2932_ = lean_nat_dec_lt(v___x_2930_, v___x_2931_);
lean_dec(v___x_2930_);
if (v___x_2932_ == 0)
{
lean_object* v_ks_2933_; lean_object* v_vs_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_ks_2933_ = lean_ctor_get(v_newNode_2927_, 0);
lean_inc_ref(v_ks_2933_);
v_vs_2934_ = lean_ctor_get(v_newNode_2927_, 1);
lean_inc_ref(v_vs_2934_);
lean_dec_ref(v_newNode_2927_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2864_, v_ks_2933_, v_vs_2934_, v___x_2935_, v___x_2936_);
lean_dec_ref(v_vs_2934_);
lean_dec_ref(v_ks_2933_);
return v___x_2937_;
}
else
{
return v_newNode_2927_;
}
}
else
{
return v_newNode_2927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2940_, lean_object* v_keys_2941_, lean_object* v_vals_2942_, lean_object* v_i_2943_, lean_object* v_entries_2944_){
_start:
{
lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = lean_array_get_size(v_keys_2941_);
v___x_2946_ = lean_nat_dec_lt(v_i_2943_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec(v_i_2943_);
return v_entries_2944_;
}
else
{
lean_object* v_k_2947_; lean_object* v_expr_2948_; uint64_t v_configKey_2949_; lean_object* v_v_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; size_t v_h_2953_; size_t v___x_2954_; lean_object* v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; size_t v_h_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_k_2947_ = lean_array_fget_borrowed(v_keys_2941_, v_i_2943_);
v_expr_2948_ = lean_ctor_get(v_k_2947_, 0);
v_configKey_2949_ = lean_ctor_get_uint64(v_k_2947_, sizeof(void*)*1);
v_v_2950_ = lean_array_fget_borrowed(v_vals_2942_, v_i_2943_);
v___x_2951_ = l_Lean_Expr_hash(v_expr_2948_);
v___x_2952_ = lean_uint64_mix_hash(v___x_2951_, v_configKey_2949_);
v_h_2953_ = lean_uint64_to_usize(v___x_2952_);
v___x_2954_ = ((size_t)5ULL);
v___x_2955_ = lean_unsigned_to_nat(1u);
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_sub(v_depth_2940_, v___x_2956_);
v___x_2958_ = lean_usize_mul(v___x_2954_, v___x_2957_);
v_h_2959_ = lean_usize_shift_right(v_h_2953_, v___x_2958_);
v___x_2960_ = lean_nat_add(v_i_2943_, v___x_2955_);
lean_dec(v_i_2943_);
lean_inc(v_v_2950_);
lean_inc(v_k_2947_);
v___x_2961_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2944_, v_h_2959_, v_depth_2940_, v_k_2947_, v_v_2950_);
v_i_2943_ = v___x_2960_;
v_entries_2944_ = v___x_2961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2963_, lean_object* v_keys_2964_, lean_object* v_vals_2965_, lean_object* v_i_2966_, lean_object* v_entries_2967_){
_start:
{
size_t v_depth_boxed_2968_; lean_object* v_res_2969_; 
v_depth_boxed_2968_ = lean_unbox_usize(v_depth_2963_);
lean_dec(v_depth_2963_);
v_res_2969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2968_, v_keys_2964_, v_vals_2965_, v_i_2966_, v_entries_2967_);
lean_dec_ref(v_vals_2965_);
lean_dec_ref(v_keys_2964_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2970_, lean_object* v_x_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
size_t v_x_2761__boxed_2975_; size_t v_x_2762__boxed_2976_; lean_object* v_res_2977_; 
v_x_2761__boxed_2975_ = lean_unbox_usize(v_x_2971_);
lean_dec(v_x_2971_);
v_x_2762__boxed_2976_ = lean_unbox_usize(v_x_2972_);
lean_dec(v_x_2972_);
v_res_2977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2970_, v_x_2761__boxed_2975_, v_x_2762__boxed_2976_, v_x_2973_, v_x_2974_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v_expr_2981_; uint64_t v_configKey_2982_; uint64_t v___x_2983_; uint64_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v_expr_2981_ = lean_ctor_get(v_x_2979_, 0);
v_configKey_2982_ = lean_ctor_get_uint64(v_x_2979_, sizeof(void*)*1);
v___x_2983_ = l_Lean_Expr_hash(v_expr_2981_);
v___x_2984_ = lean_uint64_mix_hash(v___x_2983_, v_configKey_2982_);
v___x_2985_ = lean_uint64_to_usize(v___x_2984_);
v___x_2986_ = ((size_t)1ULL);
v___x_2987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2978_, v___x_2985_, v___x_2986_, v_x_2979_, v_x_2980_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2988_, lean_object* v_vals_2989_, lean_object* v_i_2990_, lean_object* v_k_2991_){
_start:
{
uint8_t v___y_2993_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = lean_array_get_size(v_keys_2988_);
v___x_3000_ = lean_nat_dec_lt(v_i_2990_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_i_2990_);
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
lean_object* v_expr_3002_; uint64_t v_configKey_3003_; lean_object* v_k_x27_3004_; lean_object* v_expr_3005_; uint64_t v_configKey_3006_; uint8_t v___x_3007_; 
v_expr_3002_ = lean_ctor_get(v_k_2991_, 0);
v_configKey_3003_ = lean_ctor_get_uint64(v_k_2991_, sizeof(void*)*1);
v_k_x27_3004_ = lean_array_fget_borrowed(v_keys_2988_, v_i_2990_);
v_expr_3005_ = lean_ctor_get(v_k_x27_3004_, 0);
v_configKey_3006_ = lean_ctor_get_uint64(v_k_x27_3004_, sizeof(void*)*1);
v___x_3007_ = lean_expr_equal(v_expr_3002_, v_expr_3005_);
if (v___x_3007_ == 0)
{
v___y_2993_ = v___x_3007_;
goto v___jp_2992_;
}
else
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_uint64_dec_eq(v_configKey_3003_, v_configKey_3006_);
v___y_2993_ = v___x_3008_;
goto v___jp_2992_;
}
}
v___jp_2992_:
{
if (v___y_2993_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_nat_add(v_i_2990_, v___x_2994_);
lean_dec(v_i_2990_);
v_i_2990_ = v___x_2995_;
goto _start;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_array_fget_borrowed(v_vals_2989_, v_i_2990_);
lean_dec(v_i_2990_);
lean_inc(v___x_2997_);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3009_, lean_object* v_vals_3010_, lean_object* v_i_3011_, lean_object* v_k_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3009_, v_vals_3010_, v_i_3011_, v_k_3012_);
lean_dec_ref(v_k_3012_);
lean_dec_ref(v_vals_3010_);
lean_dec_ref(v_keys_3009_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3014_, size_t v_x_3015_, lean_object* v_x_3016_){
_start:
{
if (lean_obj_tag(v_x_3014_) == 0)
{
lean_object* v_es_3017_; lean_object* v___x_3018_; size_t v___x_3019_; size_t v___x_3020_; lean_object* v_j_3021_; lean_object* v___x_3022_; 
v_es_3017_ = lean_ctor_get(v_x_3014_, 0);
v___x_3018_ = lean_box(2);
v___x_3019_ = ((size_t)31ULL);
v___x_3020_ = lean_usize_land(v_x_3015_, v___x_3019_);
v_j_3021_ = lean_usize_to_nat(v___x_3020_);
v___x_3022_ = lean_array_get_borrowed(v___x_3018_, v_es_3017_, v_j_3021_);
lean_dec(v_j_3021_);
switch(lean_obj_tag(v___x_3022_))
{
case 0:
{
lean_object* v_key_3023_; lean_object* v_val_3024_; uint8_t v___y_3026_; lean_object* v_expr_3029_; uint64_t v_configKey_3030_; lean_object* v_expr_3031_; uint64_t v_configKey_3032_; uint8_t v___x_3033_; 
v_key_3023_ = lean_ctor_get(v___x_3022_, 0);
v_val_3024_ = lean_ctor_get(v___x_3022_, 1);
v_expr_3029_ = lean_ctor_get(v_x_3016_, 0);
v_configKey_3030_ = lean_ctor_get_uint64(v_x_3016_, sizeof(void*)*1);
v_expr_3031_ = lean_ctor_get(v_key_3023_, 0);
v_configKey_3032_ = lean_ctor_get_uint64(v_key_3023_, sizeof(void*)*1);
v___x_3033_ = lean_expr_equal(v_expr_3029_, v_expr_3031_);
if (v___x_3033_ == 0)
{
v___y_3026_ = v___x_3033_;
goto v___jp_3025_;
}
else
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_uint64_dec_eq(v_configKey_3030_, v_configKey_3032_);
v___y_3026_ = v___x_3034_;
goto v___jp_3025_;
}
v___jp_3025_:
{
if (v___y_3026_ == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_box(0);
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; 
lean_inc(v_val_3024_);
v___x_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_val_3024_);
return v___x_3028_;
}
}
}
case 1:
{
lean_object* v_node_3035_; size_t v___x_3036_; size_t v___x_3037_; 
v_node_3035_ = lean_ctor_get(v___x_3022_, 0);
v___x_3036_ = ((size_t)5ULL);
v___x_3037_ = lean_usize_shift_right(v_x_3015_, v___x_3036_);
v_x_3014_ = v_node_3035_;
v_x_3015_ = v___x_3037_;
goto _start;
}
default: 
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_box(0);
return v___x_3039_;
}
}
}
else
{
lean_object* v_ks_3040_; lean_object* v_vs_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_ks_3040_ = lean_ctor_get(v_x_3014_, 0);
v_vs_3041_ = lean_ctor_get(v_x_3014_, 1);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3040_, v_vs_3041_, v___x_3042_, v_x_3016_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_){
_start:
{
size_t v_x_2966__boxed_3047_; lean_object* v_res_3048_; 
v_x_2966__boxed_3047_ = lean_unbox_usize(v_x_3045_);
lean_dec(v_x_3045_);
v_res_3048_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3044_, v_x_2966__boxed_3047_, v_x_3046_);
lean_dec_ref(v_x_3046_);
lean_dec_ref(v_x_3044_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v_expr_3051_; uint64_t v_configKey_3052_; uint64_t v___x_3053_; uint64_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v_expr_3051_ = lean_ctor_get(v_x_3050_, 0);
v_configKey_3052_ = lean_ctor_get_uint64(v_x_3050_, sizeof(void*)*1);
v___x_3053_ = l_Lean_Expr_hash(v_expr_3051_);
v___x_3054_ = lean_uint64_mix_hash(v___x_3053_, v_configKey_3052_);
v___x_3055_ = lean_uint64_to_usize(v___x_3054_);
v___x_3056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3049_, v___x_3055_, v_x_3050_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3057_, lean_object* v_x_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3057_, v_x_3058_);
lean_dec_ref(v_x_3058_);
lean_dec_ref(v_x_3057_);
return v_res_3059_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3062_ = l_Lean_stringToMessageData(v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
switch(lean_obj_tag(v_e_3063_))
{
case 0:
{
lean_object* v_deBruijnIndex_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_deBruijnIndex_3099_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_deBruijnIndex_3099_);
lean_dec_ref_known(v_e_3063_, 1);
v___x_3100_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3101_ = l_Lean_mkBVar(v_deBruijnIndex_3099_);
v___x_3102_ = l_Lean_MessageData_ofExpr(v___x_3101_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3100_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3103_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3104_;
}
case 1:
{
lean_object* v_fvarId_3105_; lean_object* v___x_3106_; 
v_fvarId_3105_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_fvarId_3105_);
lean_dec_ref_known(v_e_3063_, 1);
v___x_3106_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3105_, v_a_3064_, v_a_3066_, v_a_3067_);
return v___x_3106_;
}
case 2:
{
lean_object* v_mvarId_3107_; lean_object* v___x_3108_; 
v_mvarId_3107_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_mvarId_3107_);
lean_dec_ref_known(v_e_3063_, 1);
v___x_3108_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3107_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3108_;
}
case 3:
{
lean_object* v_u_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_u_3109_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_u_3109_);
lean_dec_ref_known(v_e_3063_, 1);
v___x_3110_ = l_Lean_Level_succ___override(v_u_3109_);
v___x_3111_ = l_Lean_mkSort(v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
case 4:
{
lean_object* v_declName_3113_; lean_object* v_us_3114_; 
v_declName_3113_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_declName_3113_);
v_us_3114_ = lean_ctor_get(v_e_3063_, 1);
lean_inc(v_us_3114_);
if (lean_obj_tag(v_us_3114_) == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref_known(v_e_3063_, 2);
v___x_3130_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3113_, v_us_3114_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3130_;
}
else
{
uint8_t v_cacheInferType_3131_; 
v_cacheInferType_3131_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3131_ == 0)
{
lean_dec_ref_known(v_e_3063_, 2);
goto v___jp_3115_;
}
else
{
uint8_t v___x_3132_; 
v___x_3132_ = l_Lean_Expr_hasMVar(v_e_3063_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3198_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3198_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3198_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3178_; lean_object* v_cache_3179_; lean_object* v_inferType_3180_; lean_object* v___x_3181_; 
v___x_3178_ = lean_st_ref_get(v_a_3065_);
v_cache_3179_ = lean_ctor_get(v___x_3178_, 1);
lean_inc_ref(v_cache_3179_);
lean_dec(v___x_3178_);
v_inferType_3180_ = lean_ctor_get(v_cache_3179_, 0);
lean_inc_ref(v_inferType_3180_);
lean_dec_ref(v_cache_3179_);
v___x_3181_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3180_, v_a_3134_);
lean_dec_ref(v_inferType_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_cancelTk_x3f_3182_; 
lean_del_object(v___x_3136_);
v_cancelTk_x3f_3182_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3182_) == 1)
{
lean_object* v_val_3183_; uint8_t v___x_3184_; 
v_val_3183_ = lean_ctor_get(v_cancelTk_x3f_3182_, 0);
v___x_3184_ = l_IO_CancelToken_isSet(v_val_3183_);
if (v___x_3184_ == 0)
{
goto v___jp_3138_;
}
else
{
lean_object* v___x_3185_; lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_a_3134_);
lean_dec(v_us_3114_);
lean_dec(v_declName_3113_);
v___x_3185_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
goto v___jp_3138_;
}
}
else
{
lean_object* v_val_3194_; lean_object* v___x_3196_; 
lean_dec(v_a_3134_);
lean_dec(v_us_3114_);
lean_dec(v_declName_3113_);
v_val_3194_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v___x_3181_, 1);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_val_3194_);
v___x_3196_ = v___x_3136_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_val_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
v___jp_3138_:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3113_, v_us_3114_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; uint8_t v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
v___x_3141_ = l_Lean_Expr_hasMVar(v_a_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3176_; 
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3177_);
v___x_3143_ = v___x_3139_;
v_isShared_3144_ = v_isSharedCheck_3176_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v___x_3139_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3176_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v_cache_3146_; lean_object* v_mctx_3147_; lean_object* v_zetaDeltaFVarIds_3148_; lean_object* v_postponed_3149_; lean_object* v_diag_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3175_; 
v___x_3145_ = lean_st_ref_take(v_a_3065_);
v_cache_3146_ = lean_ctor_get(v___x_3145_, 1);
v_mctx_3147_ = lean_ctor_get(v___x_3145_, 0);
v_zetaDeltaFVarIds_3148_ = lean_ctor_get(v___x_3145_, 2);
v_postponed_3149_ = lean_ctor_get(v___x_3145_, 3);
v_diag_3150_ = lean_ctor_get(v___x_3145_, 4);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3152_ = v___x_3145_;
v_isShared_3153_ = v_isSharedCheck_3175_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_diag_3150_);
lean_inc(v_postponed_3149_);
lean_inc(v_zetaDeltaFVarIds_3148_);
lean_inc(v_cache_3146_);
lean_inc(v_mctx_3147_);
lean_dec(v___x_3145_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3175_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_inferType_3154_; lean_object* v_funInfo_3155_; lean_object* v_synthInstance_3156_; lean_object* v_whnf_3157_; lean_object* v_defEqTrans_3158_; lean_object* v_defEqPerm_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3174_; 
v_inferType_3154_ = lean_ctor_get(v_cache_3146_, 0);
v_funInfo_3155_ = lean_ctor_get(v_cache_3146_, 1);
v_synthInstance_3156_ = lean_ctor_get(v_cache_3146_, 2);
v_whnf_3157_ = lean_ctor_get(v_cache_3146_, 3);
v_defEqTrans_3158_ = lean_ctor_get(v_cache_3146_, 4);
v_defEqPerm_3159_ = lean_ctor_get(v_cache_3146_, 5);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_cache_3146_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3161_ = v_cache_3146_;
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_defEqPerm_3159_);
lean_inc(v_defEqTrans_3158_);
lean_inc(v_whnf_3157_);
lean_inc(v_synthInstance_3156_);
lean_inc(v_funInfo_3155_);
lean_inc(v_inferType_3154_);
lean_dec(v_cache_3146_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_inc(v_a_3140_);
v___x_3163_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3154_, v_a_3134_, v_a_3140_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_funInfo_3155_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_synthInstance_3156_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_whnf_3157_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_defEqTrans_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v_defEqPerm_3159_);
v___x_3165_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 1, v___x_3165_);
v___x_3167_ = v___x_3152_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_mctx_3147_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_zetaDeltaFVarIds_3148_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_postponed_3149_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_diag_3150_);
v___x_3167_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_st_ref_put(v_a_3065_, v___x_3167_);
if (v_isShared_3144_ == 0)
{
v___x_3170_ = v___x_3143_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3140_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3140_);
lean_dec(v_a_3134_);
return v___x_3139_;
}
}
else
{
lean_dec(v_a_3134_);
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_us_3114_);
lean_dec(v_declName_3113_);
v_a_3199_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3133_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3133_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3063_, 2);
goto v___jp_3115_;
}
}
}
v___jp_3115_:
{
lean_object* v_cancelTk_x3f_3116_; 
v_cancelTk_x3f_3116_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3116_) == 1)
{
lean_object* v_val_3117_; uint8_t v___x_3118_; 
v_val_3117_ = lean_ctor_get(v_cancelTk_x3f_3116_, 0);
v___x_3118_ = l_IO_CancelToken_isSet(v_val_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3113_, v_us_3114_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_us_3114_);
lean_dec(v_declName_3113_);
v___x_3120_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v___x_3129_; 
v___x_3129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3113_, v_us_3114_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3129_;
}
}
}
case 5:
{
lean_object* v_fn_3207_; uint8_t v_cacheInferType_3208_; lean_object* v_nargs_3209_; lean_object* v___x_3210_; lean_object* v_dummy_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_fn_3207_ = lean_ctor_get(v_e_3063_, 0);
v_cacheInferType_3208_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*7 + 3);
v_nargs_3209_ = l_Lean_Expr_getAppNumArgs(v_e_3063_);
v___x_3210_ = l_Lean_Expr_getAppFn(v_fn_3207_);
v_dummy_3211_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3209_);
v___x_3212_ = lean_mk_array(v_nargs_3209_, v_dummy_3211_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_sub(v_nargs_3209_, v___x_3213_);
lean_dec(v_nargs_3209_);
lean_inc_ref(v_e_3063_);
v___x_3215_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3063_, v___x_3212_, v___x_3214_);
if (v_cacheInferType_3208_ == 0)
{
lean_dec_ref_known(v_e_3063_, 2);
goto v___jp_3216_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Lean_Expr_hasMVar(v_e_3063_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3297_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3297_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3297_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3277_; lean_object* v_cache_3278_; lean_object* v_inferType_3279_; lean_object* v___x_3280_; 
v___x_3277_ = lean_st_ref_get(v_a_3065_);
v_cache_3278_ = lean_ctor_get(v___x_3277_, 1);
lean_inc_ref(v_cache_3278_);
lean_dec(v___x_3277_);
v_inferType_3279_ = lean_ctor_get(v_cache_3278_, 0);
lean_inc_ref(v_inferType_3279_);
lean_dec_ref(v_cache_3278_);
v___x_3280_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3279_, v_a_3233_);
lean_dec_ref(v_inferType_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_cancelTk_x3f_3281_; 
lean_del_object(v___x_3235_);
v_cancelTk_x3f_3281_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3281_) == 1)
{
lean_object* v_val_3282_; uint8_t v___x_3283_; 
v_val_3282_ = lean_ctor_get(v_cancelTk_x3f_3281_, 0);
v___x_3283_ = l_IO_CancelToken_isSet(v_val_3282_);
if (v___x_3283_ == 0)
{
goto v___jp_3237_;
}
else
{
lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_a_3233_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3210_);
v___x_3284_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
goto v___jp_3237_;
}
}
else
{
lean_object* v_val_3293_; lean_object* v___x_3295_; 
lean_dec(v_a_3233_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3210_);
v_val_3293_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___x_3280_, 1);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v_val_3293_);
v___x_3295_ = v___x_3235_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_val_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
v___jp_3237_:
{
lean_object* v___x_3238_; 
v___x_3238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3210_, v___x_3215_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec_ref(v___x_3215_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; uint8_t v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
v___x_3240_ = l_Lean_Expr_hasMVar(v_a_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3275_; 
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3275_ == 0)
{
lean_object* v_unused_3276_; 
v_unused_3276_ = lean_ctor_get(v___x_3238_, 0);
lean_dec(v_unused_3276_);
v___x_3242_ = v___x_3238_;
v_isShared_3243_ = v_isSharedCheck_3275_;
goto v_resetjp_3241_;
}
else
{
lean_dec(v___x_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3275_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v_cache_3245_; lean_object* v_mctx_3246_; lean_object* v_zetaDeltaFVarIds_3247_; lean_object* v_postponed_3248_; lean_object* v_diag_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3274_; 
v___x_3244_ = lean_st_ref_take(v_a_3065_);
v_cache_3245_ = lean_ctor_get(v___x_3244_, 1);
v_mctx_3246_ = lean_ctor_get(v___x_3244_, 0);
v_zetaDeltaFVarIds_3247_ = lean_ctor_get(v___x_3244_, 2);
v_postponed_3248_ = lean_ctor_get(v___x_3244_, 3);
v_diag_3249_ = lean_ctor_get(v___x_3244_, 4);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3251_ = v___x_3244_;
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_diag_3249_);
lean_inc(v_postponed_3248_);
lean_inc(v_zetaDeltaFVarIds_3247_);
lean_inc(v_cache_3245_);
lean_inc(v_mctx_3246_);
lean_dec(v___x_3244_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_inferType_3253_; lean_object* v_funInfo_3254_; lean_object* v_synthInstance_3255_; lean_object* v_whnf_3256_; lean_object* v_defEqTrans_3257_; lean_object* v_defEqPerm_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3273_; 
v_inferType_3253_ = lean_ctor_get(v_cache_3245_, 0);
v_funInfo_3254_ = lean_ctor_get(v_cache_3245_, 1);
v_synthInstance_3255_ = lean_ctor_get(v_cache_3245_, 2);
v_whnf_3256_ = lean_ctor_get(v_cache_3245_, 3);
v_defEqTrans_3257_ = lean_ctor_get(v_cache_3245_, 4);
v_defEqPerm_3258_ = lean_ctor_get(v_cache_3245_, 5);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_cache_3245_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3260_ = v_cache_3245_;
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_defEqPerm_3258_);
lean_inc(v_defEqTrans_3257_);
lean_inc(v_whnf_3256_);
lean_inc(v_synthInstance_3255_);
lean_inc(v_funInfo_3254_);
lean_inc(v_inferType_3253_);
lean_dec(v_cache_3245_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_inc(v_a_3239_);
v___x_3262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3253_, v_a_3233_, v_a_3239_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_funInfo_3254_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_synthInstance_3255_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_whnf_3256_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_defEqTrans_3257_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_defEqPerm_3258_);
v___x_3264_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3266_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v___x_3264_);
v___x_3266_ = v___x_3251_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_mctx_3246_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_zetaDeltaFVarIds_3247_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_postponed_3248_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_diag_3249_);
v___x_3266_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3267_ = lean_st_ref_put(v_a_3065_, v___x_3266_);
if (v_isShared_3243_ == 0)
{
v___x_3269_ = v___x_3242_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3239_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3239_);
lean_dec(v_a_3233_);
return v___x_3238_;
}
}
else
{
lean_dec(v_a_3233_);
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3210_);
v_a_3298_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3232_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3232_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3063_, 2);
goto v___jp_3216_;
}
}
v___jp_3216_:
{
lean_object* v_cancelTk_x3f_3217_; 
v_cancelTk_x3f_3217_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3217_) == 1)
{
lean_object* v_val_3218_; uint8_t v___x_3219_; 
v_val_3218_ = lean_ctor_get(v_cancelTk_x3f_3217_, 0);
v___x_3219_ = l_IO_CancelToken_isSet(v_val_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3210_, v___x_3215_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec_ref(v___x_3215_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3210_);
v___x_3221_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3210_, v___x_3215_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec_ref(v___x_3215_);
return v___x_3230_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3306_; 
v_cacheInferType_3306_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3306_ == 0)
{
goto v___jp_3084_;
}
else
{
uint8_t v___x_3307_; 
v___x_3307_ = l_Lean_Expr_hasMVar(v_e_3063_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_inc_ref(v_e_3063_);
v___x_3308_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3373_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3373_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3373_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3353_; lean_object* v_cache_3354_; lean_object* v_inferType_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_st_ref_get(v_a_3065_);
v_cache_3354_ = lean_ctor_get(v___x_3353_, 1);
lean_inc_ref(v_cache_3354_);
lean_dec(v___x_3353_);
v_inferType_3355_ = lean_ctor_get(v_cache_3354_, 0);
lean_inc_ref(v_inferType_3355_);
lean_dec_ref(v_cache_3354_);
v___x_3356_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3355_, v_a_3309_);
lean_dec_ref(v_inferType_3355_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_cancelTk_x3f_3357_; 
lean_del_object(v___x_3311_);
v_cancelTk_x3f_3357_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3357_) == 1)
{
lean_object* v_val_3358_; uint8_t v___x_3359_; 
v_val_3358_ = lean_ctor_get(v_cancelTk_x3f_3357_, 0);
v___x_3359_ = l_IO_CancelToken_isSet(v_val_3358_);
if (v___x_3359_ == 0)
{
goto v___jp_3313_;
}
else
{
lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3309_);
lean_dec_ref_known(v_e_3063_, 3);
v___x_3360_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
goto v___jp_3313_;
}
}
else
{
lean_object* v_val_3369_; lean_object* v___x_3371_; 
lean_dec(v_a_3309_);
lean_dec_ref_known(v_e_3063_, 3);
v_val_3369_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3356_, 1);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_val_3369_);
v___x_3371_ = v___x_3311_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_val_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
v___jp_3313_:
{
lean_object* v___x_3314_; 
v___x_3314_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; uint8_t v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
v___x_3316_ = l_Lean_Expr_hasMVar(v_a_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3351_; 
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; 
v_unused_3352_ = lean_ctor_get(v___x_3314_, 0);
lean_dec(v_unused_3352_);
v___x_3318_ = v___x_3314_;
v_isShared_3319_ = v_isSharedCheck_3351_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v___x_3314_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3351_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v_cache_3321_; lean_object* v_mctx_3322_; lean_object* v_zetaDeltaFVarIds_3323_; lean_object* v_postponed_3324_; lean_object* v_diag_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3350_; 
v___x_3320_ = lean_st_ref_take(v_a_3065_);
v_cache_3321_ = lean_ctor_get(v___x_3320_, 1);
v_mctx_3322_ = lean_ctor_get(v___x_3320_, 0);
v_zetaDeltaFVarIds_3323_ = lean_ctor_get(v___x_3320_, 2);
v_postponed_3324_ = lean_ctor_get(v___x_3320_, 3);
v_diag_3325_ = lean_ctor_get(v___x_3320_, 4);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3327_ = v___x_3320_;
v_isShared_3328_ = v_isSharedCheck_3350_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_diag_3325_);
lean_inc(v_postponed_3324_);
lean_inc(v_zetaDeltaFVarIds_3323_);
lean_inc(v_cache_3321_);
lean_inc(v_mctx_3322_);
lean_dec(v___x_3320_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3350_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_inferType_3329_; lean_object* v_funInfo_3330_; lean_object* v_synthInstance_3331_; lean_object* v_whnf_3332_; lean_object* v_defEqTrans_3333_; lean_object* v_defEqPerm_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3349_; 
v_inferType_3329_ = lean_ctor_get(v_cache_3321_, 0);
v_funInfo_3330_ = lean_ctor_get(v_cache_3321_, 1);
v_synthInstance_3331_ = lean_ctor_get(v_cache_3321_, 2);
v_whnf_3332_ = lean_ctor_get(v_cache_3321_, 3);
v_defEqTrans_3333_ = lean_ctor_get(v_cache_3321_, 4);
v_defEqPerm_3334_ = lean_ctor_get(v_cache_3321_, 5);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_cache_3321_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3336_ = v_cache_3321_;
v_isShared_3337_ = v_isSharedCheck_3349_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_defEqPerm_3334_);
lean_inc(v_defEqTrans_3333_);
lean_inc(v_whnf_3332_);
lean_inc(v_synthInstance_3331_);
lean_inc(v_funInfo_3330_);
lean_inc(v_inferType_3329_);
lean_dec(v_cache_3321_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3349_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
lean_inc(v_a_3315_);
v___x_3338_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3329_, v_a_3309_, v_a_3315_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_funInfo_3330_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_synthInstance_3331_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_whnf_3332_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_defEqTrans_3333_);
lean_ctor_set(v_reuseFailAlloc_3348_, 5, v_defEqPerm_3334_);
v___x_3340_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3340_);
v___x_3342_ = v___x_3327_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_mctx_3322_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_zetaDeltaFVarIds_3323_);
lean_ctor_set(v_reuseFailAlloc_3347_, 3, v_postponed_3324_);
lean_ctor_set(v_reuseFailAlloc_3347_, 4, v_diag_3325_);
v___x_3342_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_st_ref_put(v_a_3065_, v___x_3342_);
if (v_isShared_3319_ == 0)
{
v___x_3345_ = v___x_3318_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3315_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3315_);
lean_dec(v_a_3309_);
return v___x_3314_;
}
}
else
{
lean_dec(v_a_3309_);
return v___x_3314_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref_known(v_e_3063_, 3);
v_a_3374_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3308_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3308_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
goto v___jp_3084_;
}
}
}
case 9:
{
lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_a_3382_ = lean_ctor_get(v_e_3063_, 0);
lean_inc_ref(v_a_3382_);
lean_dec_ref_known(v_e_3063_, 1);
v___x_3383_ = l_Lean_Literal_type(v_a_3382_);
lean_dec_ref(v_a_3382_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
return v___x_3384_;
}
case 10:
{
lean_object* v_expr_3385_; 
v_expr_3385_ = lean_ctor_get(v_e_3063_, 1);
lean_inc_ref(v_expr_3385_);
lean_dec_ref_known(v_e_3063_, 2);
v_e_3063_ = v_expr_3385_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3387_; lean_object* v_idx_3388_; lean_object* v_struct_3389_; uint8_t v_cacheInferType_3405_; 
v_typeName_3387_ = lean_ctor_get(v_e_3063_, 0);
lean_inc(v_typeName_3387_);
v_idx_3388_ = lean_ctor_get(v_e_3063_, 1);
lean_inc(v_idx_3388_);
v_struct_3389_ = lean_ctor_get(v_e_3063_, 2);
lean_inc_ref(v_struct_3389_);
v_cacheInferType_3405_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3405_ == 0)
{
lean_dec_ref_known(v_e_3063_, 3);
goto v___jp_3390_;
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = l_Lean_Expr_hasMVar(v_e_3063_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3472_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3472_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3472_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3452_; lean_object* v_cache_3453_; lean_object* v_inferType_3454_; lean_object* v___x_3455_; 
v___x_3452_ = lean_st_ref_get(v_a_3065_);
v_cache_3453_ = lean_ctor_get(v___x_3452_, 1);
lean_inc_ref(v_cache_3453_);
lean_dec(v___x_3452_);
v_inferType_3454_ = lean_ctor_get(v_cache_3453_, 0);
lean_inc_ref(v_inferType_3454_);
lean_dec_ref(v_cache_3453_);
v___x_3455_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3454_, v_a_3408_);
lean_dec_ref(v_inferType_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_cancelTk_x3f_3456_; 
lean_del_object(v___x_3410_);
v_cancelTk_x3f_3456_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3456_) == 1)
{
lean_object* v_val_3457_; uint8_t v___x_3458_; 
v_val_3457_ = lean_ctor_get(v_cancelTk_x3f_3456_, 0);
v___x_3458_ = l_IO_CancelToken_isSet(v_val_3457_);
if (v___x_3458_ == 0)
{
goto v___jp_3412_;
}
else
{
lean_object* v___x_3459_; lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec(v_a_3408_);
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v___x_3459_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
goto v___jp_3412_;
}
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; 
lean_dec(v_a_3408_);
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v_val_3468_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___x_3455_, 1);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v_val_3468_);
v___x_3470_ = v___x_3410_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_val_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
v___jp_3412_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; uint8_t v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
v___x_3415_ = l_Lean_Expr_hasMVar(v_a_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3450_; 
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v___x_3413_, 0);
lean_dec(v_unused_3451_);
v___x_3417_ = v___x_3413_;
v_isShared_3418_ = v_isSharedCheck_3450_;
goto v_resetjp_3416_;
}
else
{
lean_dec(v___x_3413_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3450_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v_cache_3420_; lean_object* v_mctx_3421_; lean_object* v_zetaDeltaFVarIds_3422_; lean_object* v_postponed_3423_; lean_object* v_diag_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3449_; 
v___x_3419_ = lean_st_ref_take(v_a_3065_);
v_cache_3420_ = lean_ctor_get(v___x_3419_, 1);
v_mctx_3421_ = lean_ctor_get(v___x_3419_, 0);
v_zetaDeltaFVarIds_3422_ = lean_ctor_get(v___x_3419_, 2);
v_postponed_3423_ = lean_ctor_get(v___x_3419_, 3);
v_diag_3424_ = lean_ctor_get(v___x_3419_, 4);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3426_ = v___x_3419_;
v_isShared_3427_ = v_isSharedCheck_3449_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_diag_3424_);
lean_inc(v_postponed_3423_);
lean_inc(v_zetaDeltaFVarIds_3422_);
lean_inc(v_cache_3420_);
lean_inc(v_mctx_3421_);
lean_dec(v___x_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3449_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_inferType_3428_; lean_object* v_funInfo_3429_; lean_object* v_synthInstance_3430_; lean_object* v_whnf_3431_; lean_object* v_defEqTrans_3432_; lean_object* v_defEqPerm_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3448_; 
v_inferType_3428_ = lean_ctor_get(v_cache_3420_, 0);
v_funInfo_3429_ = lean_ctor_get(v_cache_3420_, 1);
v_synthInstance_3430_ = lean_ctor_get(v_cache_3420_, 2);
v_whnf_3431_ = lean_ctor_get(v_cache_3420_, 3);
v_defEqTrans_3432_ = lean_ctor_get(v_cache_3420_, 4);
v_defEqPerm_3433_ = lean_ctor_get(v_cache_3420_, 5);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_cache_3420_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3435_ = v_cache_3420_;
v_isShared_3436_ = v_isSharedCheck_3448_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_defEqPerm_3433_);
lean_inc(v_defEqTrans_3432_);
lean_inc(v_whnf_3431_);
lean_inc(v_synthInstance_3430_);
lean_inc(v_funInfo_3429_);
lean_inc(v_inferType_3428_);
lean_dec(v_cache_3420_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3448_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
lean_inc(v_a_3414_);
v___x_3437_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3428_, v_a_3408_, v_a_3414_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3437_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_funInfo_3429_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_synthInstance_3430_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_whnf_3431_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_defEqTrans_3432_);
lean_ctor_set(v_reuseFailAlloc_3447_, 5, v_defEqPerm_3433_);
v___x_3439_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v___x_3439_);
v___x_3441_ = v___x_3426_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_mctx_3421_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_zetaDeltaFVarIds_3422_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_postponed_3423_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_diag_3424_);
v___x_3441_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_st_ref_put(v_a_3065_, v___x_3441_);
if (v_isShared_3418_ == 0)
{
v___x_3444_ = v___x_3417_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3414_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3414_);
lean_dec(v_a_3408_);
return v___x_3413_;
}
}
else
{
lean_dec(v_a_3408_);
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v_a_3473_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3407_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3407_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3063_, 3);
goto v___jp_3390_;
}
}
v___jp_3390_:
{
lean_object* v_cancelTk_x3f_3391_; 
v_cancelTk_x3f_3391_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3391_) == 1)
{
lean_object* v_val_3392_; uint8_t v___x_3393_; 
v_val_3392_ = lean_ctor_get(v_cancelTk_x3f_3391_, 0);
v___x_3393_ = l_IO_CancelToken_isSet(v_val_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v___x_3395_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v___x_3404_; 
v___x_3404_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3404_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3481_; 
v_cacheInferType_3481_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3481_ == 0)
{
goto v___jp_3069_;
}
else
{
uint8_t v___x_3482_; 
v___x_3482_ = l_Lean_Expr_hasMVar(v_e_3063_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_inc_ref(v_e_3063_);
v___x_3483_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3548_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3548_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3548_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3528_; lean_object* v_cache_3529_; lean_object* v_inferType_3530_; lean_object* v___x_3531_; 
v___x_3528_ = lean_st_ref_get(v_a_3065_);
v_cache_3529_ = lean_ctor_get(v___x_3528_, 1);
lean_inc_ref(v_cache_3529_);
lean_dec(v___x_3528_);
v_inferType_3530_ = lean_ctor_get(v_cache_3529_, 0);
lean_inc_ref(v_inferType_3530_);
lean_dec_ref(v_cache_3529_);
v___x_3531_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3530_, v_a_3484_);
lean_dec_ref(v_inferType_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_cancelTk_x3f_3532_; 
lean_del_object(v___x_3486_);
v_cancelTk_x3f_3532_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3532_) == 1)
{
lean_object* v_val_3533_; uint8_t v___x_3534_; 
v_val_3533_ = lean_ctor_get(v_cancelTk_x3f_3532_, 0);
v___x_3534_ = l_IO_CancelToken_isSet(v_val_3533_);
if (v___x_3534_ == 0)
{
goto v___jp_3488_;
}
else
{
lean_object* v___x_3535_; lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_a_3484_);
lean_dec_ref(v_e_3063_);
v___x_3535_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
goto v___jp_3488_;
}
}
else
{
lean_object* v_val_3544_; lean_object* v___x_3546_; 
lean_dec(v_a_3484_);
lean_dec_ref(v_e_3063_);
v_val_3544_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v___x_3531_, 1);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v_val_3544_);
v___x_3546_ = v___x_3486_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_val_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
v___jp_3488_:
{
lean_object* v___x_3489_; 
v___x_3489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; uint8_t v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
v___x_3491_ = l_Lean_Expr_hasMVar(v_a_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3526_; 
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; 
v_unused_3527_ = lean_ctor_get(v___x_3489_, 0);
lean_dec(v_unused_3527_);
v___x_3493_ = v___x_3489_;
v_isShared_3494_ = v_isSharedCheck_3526_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v___x_3489_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3526_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v_cache_3496_; lean_object* v_mctx_3497_; lean_object* v_zetaDeltaFVarIds_3498_; lean_object* v_postponed_3499_; lean_object* v_diag_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3525_; 
v___x_3495_ = lean_st_ref_take(v_a_3065_);
v_cache_3496_ = lean_ctor_get(v___x_3495_, 1);
v_mctx_3497_ = lean_ctor_get(v___x_3495_, 0);
v_zetaDeltaFVarIds_3498_ = lean_ctor_get(v___x_3495_, 2);
v_postponed_3499_ = lean_ctor_get(v___x_3495_, 3);
v_diag_3500_ = lean_ctor_get(v___x_3495_, 4);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3502_ = v___x_3495_;
v_isShared_3503_ = v_isSharedCheck_3525_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_diag_3500_);
lean_inc(v_postponed_3499_);
lean_inc(v_zetaDeltaFVarIds_3498_);
lean_inc(v_cache_3496_);
lean_inc(v_mctx_3497_);
lean_dec(v___x_3495_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3525_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_inferType_3504_; lean_object* v_funInfo_3505_; lean_object* v_synthInstance_3506_; lean_object* v_whnf_3507_; lean_object* v_defEqTrans_3508_; lean_object* v_defEqPerm_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3524_; 
v_inferType_3504_ = lean_ctor_get(v_cache_3496_, 0);
v_funInfo_3505_ = lean_ctor_get(v_cache_3496_, 1);
v_synthInstance_3506_ = lean_ctor_get(v_cache_3496_, 2);
v_whnf_3507_ = lean_ctor_get(v_cache_3496_, 3);
v_defEqTrans_3508_ = lean_ctor_get(v_cache_3496_, 4);
v_defEqPerm_3509_ = lean_ctor_get(v_cache_3496_, 5);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_cache_3496_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3511_ = v_cache_3496_;
v_isShared_3512_ = v_isSharedCheck_3524_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_defEqPerm_3509_);
lean_inc(v_defEqTrans_3508_);
lean_inc(v_whnf_3507_);
lean_inc(v_synthInstance_3506_);
lean_inc(v_funInfo_3505_);
lean_inc(v_inferType_3504_);
lean_dec(v_cache_3496_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3524_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_inc(v_a_3490_);
v___x_3513_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3504_, v_a_3484_, v_a_3490_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_funInfo_3505_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_synthInstance_3506_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_whnf_3507_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_defEqTrans_3508_);
lean_ctor_set(v_reuseFailAlloc_3523_, 5, v_defEqPerm_3509_);
v___x_3515_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3515_);
v___x_3517_ = v___x_3502_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_mctx_3497_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3522_, 2, v_zetaDeltaFVarIds_3498_);
lean_ctor_set(v_reuseFailAlloc_3522_, 3, v_postponed_3499_);
lean_ctor_set(v_reuseFailAlloc_3522_, 4, v_diag_3500_);
v___x_3517_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = lean_st_ref_put(v_a_3065_, v___x_3517_);
if (v_isShared_3494_ == 0)
{
v___x_3520_ = v___x_3493_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3490_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3490_);
lean_dec(v_a_3484_);
return v___x_3489_;
}
}
else
{
lean_dec(v_a_3484_);
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_e_3063_);
v_a_3549_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3483_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3483_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
goto v___jp_3069_;
}
}
}
}
v___jp_3069_:
{
lean_object* v_cancelTk_x3f_3070_; 
v_cancelTk_x3f_3070_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3070_) == 1)
{
lean_object* v_val_3071_; uint8_t v___x_3072_; 
v_val_3071_ = lean_ctor_get(v_cancelTk_x3f_3070_, 0);
v___x_3072_ = l_IO_CancelToken_isSet(v_val_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_e_3063_);
v___x_3074_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3083_;
}
}
v___jp_3084_:
{
lean_object* v_cancelTk_x3f_3085_; 
v_cancelTk_x3f_3085_ = lean_ctor_get(v_a_3066_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3085_) == 1)
{
lean_object* v_val_3086_; uint8_t v___x_3087_; 
v_val_3086_ = lean_ctor_get(v_cancelTk_x3f_3085_, 0);
v___x_3087_ = l_IO_CancelToken_isSet(v_val_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec_ref(v_e_3063_);
v___x_3089_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3565_, v_x_3566_, v_x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3570_, v_x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3573_, v_x_3574_, v_x_3575_);
lean_dec_ref(v_x_3575_);
lean_dec_ref(v_x_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3577_, lean_object* v_x_3578_, size_t v_x_3579_, size_t v_x_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3578_, v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
size_t v_x_4004__boxed_3590_; size_t v_x_4005__boxed_3591_; lean_object* v_res_3592_; 
v_x_4004__boxed_3590_ = lean_unbox_usize(v_x_3586_);
lean_dec(v_x_3586_);
v_x_4005__boxed_3591_ = lean_unbox_usize(v_x_3587_);
lean_dec(v_x_3587_);
v_res_3592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3584_, v_x_3585_, v_x_4004__boxed_3590_, v_x_4005__boxed_3591_, v_x_3588_, v_x_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3593_, lean_object* v_x_3594_, size_t v_x_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3594_, v_x_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
size_t v_x_4021__boxed_3602_; lean_object* v_res_3603_; 
v_x_4021__boxed_3602_ = lean_unbox_usize(v_x_3600_);
lean_dec(v_x_3600_);
v_res_3603_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3598_, v_x_3599_, v_x_4021__boxed_3602_, v_x_3601_);
lean_dec_ref(v_x_3601_);
lean_dec_ref(v_x_3599_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3604_, lean_object* v_n_3605_, lean_object* v_k_3606_, lean_object* v_v_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3605_, v_k_3606_, v_v_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3609_, size_t v_depth_3610_, lean_object* v_keys_3611_, lean_object* v_vals_3612_, lean_object* v_heq_3613_, lean_object* v_i_3614_, lean_object* v_entries_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3610_, v_keys_3611_, v_vals_3612_, v_i_3614_, v_entries_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3617_, lean_object* v_depth_3618_, lean_object* v_keys_3619_, lean_object* v_vals_3620_, lean_object* v_heq_3621_, lean_object* v_i_3622_, lean_object* v_entries_3623_){
_start:
{
size_t v_depth_boxed_3624_; lean_object* v_res_3625_; 
v_depth_boxed_3624_ = lean_unbox_usize(v_depth_3618_);
lean_dec(v_depth_3618_);
v_res_3625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3617_, v_depth_boxed_3624_, v_keys_3619_, v_vals_3620_, v_heq_3621_, v_i_3622_, v_entries_3623_);
lean_dec_ref(v_vals_3620_);
lean_dec_ref(v_keys_3619_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3626_, lean_object* v_keys_3627_, lean_object* v_vals_3628_, lean_object* v_heq_3629_, lean_object* v_i_3630_, lean_object* v_k_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3627_, v_vals_3628_, v_i_3630_, v_k_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_keys_3634_, lean_object* v_vals_3635_, lean_object* v_heq_3636_, lean_object* v_i_3637_, lean_object* v_k_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3633_, v_keys_3634_, v_vals_3635_, v_heq_3636_, v_i_3637_, v_k_3638_);
lean_dec_ref(v_k_3638_);
lean_dec_ref(v_vals_3635_);
lean_dec_ref(v_keys_3634_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3641_, v_x_3642_, v_x_3643_, v_x_3644_);
return v___x_3645_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = l_Lean_maxRecDepthErrorMessage;
v___x_3652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3654_ = l_Lean_MessageData_ofFormat(v___x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3656_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3657_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v___x_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v_ref_3658_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3666_, lean_object* v_ref_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3667_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3674_, lean_object* v_ref_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3674_, v_ref_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___y_3689_; uint8_t v___y_3690_; uint8_t v___y_3691_; lean_object* v___y_3692_; uint8_t v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v_fileName_3765_; lean_object* v_fileMap_3766_; lean_object* v_options_3767_; lean_object* v_currRecDepth_3768_; lean_object* v_maxRecDepth_3769_; lean_object* v_ref_3770_; lean_object* v_currNamespace_3771_; lean_object* v_openDecls_3772_; lean_object* v_initHeartbeats_3773_; lean_object* v_maxHeartbeats_3774_; lean_object* v_quotContext_3775_; lean_object* v_currMacroScope_3776_; uint8_t v_diag_3777_; lean_object* v_cancelTk_x3f_3778_; uint8_t v_suppressElabErrors_3779_; lean_object* v_inheritedTraceOptions_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3798_; 
v_fileName_3765_ = lean_ctor_get(v_a_3685_, 0);
v_fileMap_3766_ = lean_ctor_get(v_a_3685_, 1);
v_options_3767_ = lean_ctor_get(v_a_3685_, 2);
v_currRecDepth_3768_ = lean_ctor_get(v_a_3685_, 3);
v_maxRecDepth_3769_ = lean_ctor_get(v_a_3685_, 4);
v_ref_3770_ = lean_ctor_get(v_a_3685_, 5);
v_currNamespace_3771_ = lean_ctor_get(v_a_3685_, 6);
v_openDecls_3772_ = lean_ctor_get(v_a_3685_, 7);
v_initHeartbeats_3773_ = lean_ctor_get(v_a_3685_, 8);
v_maxHeartbeats_3774_ = lean_ctor_get(v_a_3685_, 9);
v_quotContext_3775_ = lean_ctor_get(v_a_3685_, 10);
v_currMacroScope_3776_ = lean_ctor_get(v_a_3685_, 11);
v_diag_3777_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*14);
v_cancelTk_x3f_3778_ = lean_ctor_get(v_a_3685_, 12);
v_suppressElabErrors_3779_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3780_ = lean_ctor_get(v_a_3685_, 13);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3685_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3782_ = v_a_3685_;
v_isShared_3783_ = v_isSharedCheck_3798_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_inheritedTraceOptions_3780_);
lean_inc(v_cancelTk_x3f_3778_);
lean_inc(v_currMacroScope_3776_);
lean_inc(v_quotContext_3775_);
lean_inc(v_maxHeartbeats_3774_);
lean_inc(v_initHeartbeats_3773_);
lean_inc(v_openDecls_3772_);
lean_inc(v_currNamespace_3771_);
lean_inc(v_ref_3770_);
lean_inc(v_maxRecDepth_3769_);
lean_inc(v_currRecDepth_3768_);
lean_inc(v_options_3767_);
lean_inc(v_fileMap_3766_);
lean_inc(v_fileName_3765_);
lean_dec(v_a_3685_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3798_;
goto v_resetjp_3781_;
}
v___jp_3688_:
{
lean_object* v___x_3701_; uint8_t v_foApprox_3702_; uint8_t v_ctxApprox_3703_; uint8_t v_quasiPatternApprox_3704_; uint8_t v_constApprox_3705_; uint8_t v_isDefEqStuckEx_3706_; uint8_t v_unificationHints_3707_; uint8_t v_proofIrrelevance_3708_; uint8_t v_assignSyntheticOpaque_3709_; uint8_t v_offsetCnstrs_3710_; uint8_t v_transparency_3711_; uint8_t v_univApprox_3712_; uint8_t v_zetaUnused_3713_; uint8_t v_canUnfoldPredicateConfig_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3728_; 
v___x_3701_ = l_Lean_Meta_Context_config(v___y_3700_);
lean_dec_ref(v___y_3700_);
v_foApprox_3702_ = lean_ctor_get_uint8(v___x_3701_, 0);
v_ctxApprox_3703_ = lean_ctor_get_uint8(v___x_3701_, 1);
v_quasiPatternApprox_3704_ = lean_ctor_get_uint8(v___x_3701_, 2);
v_constApprox_3705_ = lean_ctor_get_uint8(v___x_3701_, 3);
v_isDefEqStuckEx_3706_ = lean_ctor_get_uint8(v___x_3701_, 4);
v_unificationHints_3707_ = lean_ctor_get_uint8(v___x_3701_, 5);
v_proofIrrelevance_3708_ = lean_ctor_get_uint8(v___x_3701_, 6);
v_assignSyntheticOpaque_3709_ = lean_ctor_get_uint8(v___x_3701_, 7);
v_offsetCnstrs_3710_ = lean_ctor_get_uint8(v___x_3701_, 8);
v_transparency_3711_ = lean_ctor_get_uint8(v___x_3701_, 9);
v_univApprox_3712_ = lean_ctor_get_uint8(v___x_3701_, 11);
v_zetaUnused_3713_ = lean_ctor_get_uint8(v___x_3701_, 17);
v_canUnfoldPredicateConfig_3714_ = lean_ctor_get_uint8(v___x_3701_, 19);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3716_ = v___x_3701_;
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
else
{
lean_dec(v___x_3701_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v___x_3718_; uint8_t v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3722_; 
v___x_3718_ = 1;
v___x_3719_ = 0;
v___x_3720_ = 2;
if (v_isShared_3717_ == 0)
{
v___x_3722_ = v___x_3716_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 0, v_foApprox_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 1, v_ctxApprox_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 2, v_quasiPatternApprox_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 3, v_constApprox_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 4, v_isDefEqStuckEx_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 5, v_unificationHints_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 6, v_proofIrrelevance_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 7, v_assignSyntheticOpaque_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 8, v_offsetCnstrs_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 9, v_transparency_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 11, v_univApprox_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 17, v_zetaUnused_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, 19, v_canUnfoldPredicateConfig_3714_);
v___x_3722_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
uint64_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_ctor_set_uint8(v___x_3722_, 10, v___x_3719_);
lean_ctor_set_uint8(v___x_3722_, 12, v___x_3718_);
lean_ctor_set_uint8(v___x_3722_, 13, v___x_3718_);
lean_ctor_set_uint8(v___x_3722_, 14, v___x_3720_);
lean_ctor_set_uint8(v___x_3722_, 15, v___x_3718_);
lean_ctor_set_uint8(v___x_3722_, 16, v___x_3718_);
lean_ctor_set_uint8(v___x_3722_, 18, v___x_3718_);
v___x_3723_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set_uint64(v___x_3724_, sizeof(void*)*1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set(v___x_3725_, 1, v___y_3694_);
lean_ctor_set(v___x_3725_, 2, v___y_3697_);
lean_ctor_set(v___x_3725_, 3, v___y_3695_);
lean_ctor_set(v___x_3725_, 4, v___y_3699_);
lean_ctor_set(v___x_3725_, 5, v___y_3696_);
lean_ctor_set(v___x_3725_, 6, v___y_3692_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*7, v___y_3690_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*7 + 1, v___y_3691_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*7 + 2, v___y_3698_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*7 + 3, v___y_3693_);
v___x_3726_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3682_, v___x_3725_, v_a_3684_, v___y_3689_, v_a_3686_);
lean_dec(v_a_3686_);
lean_dec_ref(v___y_3689_);
lean_dec(v_a_3684_);
lean_dec_ref_known(v___x_3725_, 7);
return v___x_3726_;
}
}
}
v___jp_3729_:
{
lean_object* v_keyedConfig_3732_; uint8_t v_trackZetaDelta_3733_; lean_object* v_zetaDeltaSet_3734_; lean_object* v_lctx_3735_; lean_object* v_localInstances_3736_; lean_object* v_defEqCtx_x3f_3737_; lean_object* v_synthPendingDepth_3738_; lean_object* v_customCanUnfoldPredicate_x3f_3739_; uint8_t v_univApprox_3740_; uint8_t v_inTypeClassResolution_3741_; uint8_t v_cacheInferType_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3764_; 
v_keyedConfig_3732_ = lean_ctor_get(v_a_3683_, 0);
v_trackZetaDelta_3733_ = lean_ctor_get_uint8(v_a_3683_, sizeof(void*)*7);
v_zetaDeltaSet_3734_ = lean_ctor_get(v_a_3683_, 1);
v_lctx_3735_ = lean_ctor_get(v_a_3683_, 2);
v_localInstances_3736_ = lean_ctor_get(v_a_3683_, 3);
v_defEqCtx_x3f_3737_ = lean_ctor_get(v_a_3683_, 4);
v_synthPendingDepth_3738_ = lean_ctor_get(v_a_3683_, 5);
v_customCanUnfoldPredicate_x3f_3739_ = lean_ctor_get(v_a_3683_, 6);
v_univApprox_3740_ = lean_ctor_get_uint8(v_a_3683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3741_ = lean_ctor_get_uint8(v_a_3683_, sizeof(void*)*7 + 2);
v_cacheInferType_3742_ = lean_ctor_get_uint8(v_a_3683_, sizeof(void*)*7 + 3);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3683_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3744_ = v_a_3683_;
v_isShared_3745_ = v_isSharedCheck_3764_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3739_);
lean_inc(v_synthPendingDepth_3738_);
lean_inc(v_defEqCtx_x3f_3737_);
lean_inc(v_localInstances_3736_);
lean_inc(v_lctx_3735_);
lean_inc(v_zetaDeltaSet_3734_);
lean_inc(v_keyedConfig_3732_);
lean_dec(v_a_3683_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3764_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3746_; lean_object* v___x_3748_; 
v___x_3746_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_3731_, v_keyedConfig_3732_);
lean_inc(v_customCanUnfoldPredicate_x3f_3739_);
lean_inc(v_synthPendingDepth_3738_);
lean_inc(v_defEqCtx_x3f_3737_);
lean_inc_ref(v_localInstances_3736_);
lean_inc_ref(v_lctx_3735_);
lean_inc(v_zetaDeltaSet_3734_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3746_);
v___x_3748_ = v___x_3744_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_zetaDeltaSet_3734_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_lctx_3735_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_localInstances_3736_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_defEqCtx_x3f_3737_);
lean_ctor_set(v_reuseFailAlloc_3763_, 5, v_synthPendingDepth_3738_);
lean_ctor_set(v_reuseFailAlloc_3763_, 6, v_customCanUnfoldPredicate_x3f_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7, v_trackZetaDelta_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 1, v_univApprox_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 3, v_cacheInferType_3742_);
v___x_3748_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; uint8_t v_beta_3750_; 
v___x_3749_ = l_Lean_Meta_Context_config(v___x_3748_);
v_beta_3750_ = lean_ctor_get_uint8(v___x_3749_, 13);
if (v_beta_3750_ == 0)
{
lean_dec_ref(v___x_3749_);
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v_iota_3751_; 
v_iota_3751_ = lean_ctor_get_uint8(v___x_3749_, 12);
if (v_iota_3751_ == 0)
{
lean_dec_ref(v___x_3749_);
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v_zeta_3752_; 
v_zeta_3752_ = lean_ctor_get_uint8(v___x_3749_, 15);
if (v_zeta_3752_ == 0)
{
lean_dec_ref(v___x_3749_);
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v_zetaHave_3753_; 
v_zetaHave_3753_ = lean_ctor_get_uint8(v___x_3749_, 18);
if (v_zetaHave_3753_ == 0)
{
lean_dec_ref(v___x_3749_);
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v_zetaDelta_3754_; 
v_zetaDelta_3754_ = lean_ctor_get_uint8(v___x_3749_, 16);
if (v_zetaDelta_3754_ == 0)
{
lean_dec_ref(v___x_3749_);
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v_etaStruct_3755_; uint8_t v_proj_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_etaStruct_3755_ = lean_ctor_get_uint8(v___x_3749_, 10);
v_proj_3756_ = lean_ctor_get_uint8(v___x_3749_, 14);
lean_dec_ref(v___x_3749_);
v___x_3757_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_3756_);
v___x_3758_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___closed__0);
v___x_3759_ = lean_nat_dec_eq(v___x_3757_, v___x_3758_);
lean_dec(v___x_3757_);
if (v___x_3759_ == 0)
{
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
uint8_t v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = 0;
v___x_3761_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3755_, v___x_3760_);
if (v___x_3761_ == 0)
{
v___y_3689_ = v___y_3730_;
v___y_3690_ = v_trackZetaDelta_3733_;
v___y_3691_ = v_univApprox_3740_;
v___y_3692_ = v_customCanUnfoldPredicate_x3f_3739_;
v___y_3693_ = v_cacheInferType_3742_;
v___y_3694_ = v_zetaDeltaSet_3734_;
v___y_3695_ = v_localInstances_3736_;
v___y_3696_ = v_synthPendingDepth_3738_;
v___y_3697_ = v_lctx_3735_;
v___y_3698_ = v_inTypeClassResolution_3741_;
v___y_3699_ = v_defEqCtx_x3f_3737_;
v___y_3700_ = v___x_3748_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3762_; 
lean_dec(v_customCanUnfoldPredicate_x3f_3739_);
lean_dec(v_synthPendingDepth_3738_);
lean_dec(v_defEqCtx_x3f_3737_);
lean_dec_ref(v_localInstances_3736_);
lean_dec_ref(v_lctx_3735_);
lean_dec(v_zetaDeltaSet_3734_);
v___x_3762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3682_, v___x_3748_, v_a_3684_, v___y_3730_, v_a_3686_);
lean_dec(v_a_3686_);
lean_dec_ref(v___y_3730_);
lean_dec(v_a_3684_);
lean_dec_ref(v___x_3748_);
return v___x_3762_;
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
v_resetjp_3781_:
{
lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_nat_dec_eq(v_maxRecDepth_3769_, v___x_3794_);
if (v___x_3795_ == 0)
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_nat_dec_eq(v_currRecDepth_3768_, v_maxRecDepth_3769_);
if (v___x_3796_ == 0)
{
goto v___jp_3784_;
}
else
{
lean_object* v___x_3797_; 
lean_del_object(v___x_3782_);
lean_dec_ref(v_inheritedTraceOptions_3780_);
lean_dec(v_cancelTk_x3f_3778_);
lean_dec(v_currMacroScope_3776_);
lean_dec(v_quotContext_3775_);
lean_dec(v_maxHeartbeats_3774_);
lean_dec(v_initHeartbeats_3773_);
lean_dec(v_openDecls_3772_);
lean_dec(v_currNamespace_3771_);
lean_dec(v_maxRecDepth_3769_);
lean_dec(v_currRecDepth_3768_);
lean_dec_ref(v_options_3767_);
lean_dec_ref(v_fileMap_3766_);
lean_dec_ref(v_fileName_3765_);
lean_dec(v_a_3686_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec_ref(v_e_3682_);
v___x_3797_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3770_);
return v___x_3797_;
}
}
else
{
goto v___jp_3784_;
}
v___jp_3784_:
{
lean_object* v___x_3785_; uint8_t v_transparency_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3785_ = l_Lean_Meta_Context_config(v_a_3683_);
v_transparency_3786_ = lean_ctor_get_uint8(v___x_3785_, 9);
lean_dec_ref(v___x_3785_);
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_add(v_currRecDepth_3768_, v___x_3787_);
lean_dec(v_currRecDepth_3768_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 3, v___x_3788_);
v___x_3790_ = v___x_3782_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fileName_3765_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_fileMap_3766_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_options_3767_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v_maxRecDepth_3769_);
lean_ctor_set(v_reuseFailAlloc_3793_, 5, v_ref_3770_);
lean_ctor_set(v_reuseFailAlloc_3793_, 6, v_currNamespace_3771_);
lean_ctor_set(v_reuseFailAlloc_3793_, 7, v_openDecls_3772_);
lean_ctor_set(v_reuseFailAlloc_3793_, 8, v_initHeartbeats_3773_);
lean_ctor_set(v_reuseFailAlloc_3793_, 9, v_maxHeartbeats_3774_);
lean_ctor_set(v_reuseFailAlloc_3793_, 10, v_quotContext_3775_);
lean_ctor_set(v_reuseFailAlloc_3793_, 11, v_currMacroScope_3776_);
lean_ctor_set(v_reuseFailAlloc_3793_, 12, v_cancelTk_x3f_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 13, v_inheritedTraceOptions_3780_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*14, v_diag_3777_);
lean_ctor_set_uint8(v_reuseFailAlloc_3793_, sizeof(void*)*14 + 1, v_suppressElabErrors_3779_);
v___x_3790_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
uint8_t v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = 1;
v___x_3792_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3786_, v___x_3791_);
if (v___x_3792_ == 0)
{
v___y_3730_ = v___x_3790_;
v___y_3731_ = v_transparency_3786_;
goto v___jp_3729_;
}
else
{
v___y_3730_ = v___x_3790_;
v___y_3731_ = v___x_3791_;
goto v___jp_3729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = lean_infer_type(v_e_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
return v_res_3805_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3806_){
_start:
{
switch(lean_obj_tag(v_x_3806_))
{
case 0:
{
uint8_t v___x_3807_; 
v___x_3807_ = 1;
return v___x_3807_;
}
case 2:
{
lean_object* v_a_3808_; lean_object* v_a_3809_; uint8_t v___x_3810_; 
v_a_3808_ = lean_ctor_get(v_x_3806_, 0);
v_a_3809_ = lean_ctor_get(v_x_3806_, 1);
v___x_3810_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3808_);
if (v___x_3810_ == 0)
{
return v___x_3810_;
}
else
{
v_x_3806_ = v_a_3809_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3812_; 
v_a_3812_ = lean_ctor_get(v_x_3806_, 1);
v_x_3806_ = v_a_3812_;
goto _start;
}
default: 
{
uint8_t v___x_3814_; 
v___x_3814_ = 0;
return v___x_3814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3815_){
_start:
{
uint8_t v_res_3816_; lean_object* v_r_3817_; 
v_res_3816_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3815_);
lean_dec(v_x_3815_);
v_r_3817_ = lean_box(v_res_3816_);
return v_r_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v_mctx_3822_; lean_object* v___x_3823_; lean_object* v_fst_3824_; lean_object* v_snd_3825_; lean_object* v___x_3826_; lean_object* v_cache_3827_; lean_object* v_zetaDeltaFVarIds_3828_; lean_object* v_postponed_3829_; lean_object* v_diag_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3839_; 
v___x_3821_ = lean_st_ref_get(v___y_3819_);
v_mctx_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc_ref(v_mctx_3822_);
lean_dec(v___x_3821_);
v___x_3823_ = lean_instantiate_level_mvars(v_mctx_3822_, v_l_3818_);
v_fst_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_fst_3824_);
v_snd_3825_ = lean_ctor_get(v___x_3823_, 1);
lean_inc(v_snd_3825_);
lean_dec_ref(v___x_3823_);
v___x_3826_ = lean_st_ref_take(v___y_3819_);
v_cache_3827_ = lean_ctor_get(v___x_3826_, 1);
v_zetaDeltaFVarIds_3828_ = lean_ctor_get(v___x_3826_, 2);
v_postponed_3829_ = lean_ctor_get(v___x_3826_, 3);
v_diag_3830_ = lean_ctor_get(v___x_3826_, 4);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3826_, 0);
lean_dec(v_unused_3840_);
v___x_3832_ = v___x_3826_;
v_isShared_3833_ = v_isSharedCheck_3839_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_diag_3830_);
lean_inc(v_postponed_3829_);
lean_inc(v_zetaDeltaFVarIds_3828_);
lean_inc(v_cache_3827_);
lean_dec(v___x_3826_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3839_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v_fst_3824_);
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_fst_3824_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_cache_3827_);
lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_zetaDeltaFVarIds_3828_);
lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_postponed_3829_);
lean_ctor_set(v_reuseFailAlloc_3838_, 4, v_diag_3830_);
v___x_3835_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = lean_st_ref_put(v___y_3819_, v___x_3835_);
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_snd_3825_);
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3841_, v___y_3842_);
lean_dec(v___y_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3845_, v___y_3847_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3859_, lean_object* v_x_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
switch(lean_obj_tag(v_x_3859_))
{
case 3:
{
lean_object* v_u_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_u_3870_ = lean_ctor_get(v_x_3859_, 0);
lean_inc(v_u_3870_);
lean_dec_ref_known(v_x_3859_, 1);
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = lean_nat_dec_eq(v_x_3860_, v___x_3871_);
lean_dec(v_x_3860_);
if (v___x_3872_ == 0)
{
lean_dec(v_u_3870_);
goto v___jp_3866_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3870_, v_a_3862_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3884_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3884_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3884_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
uint8_t v___x_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___x_3878_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3874_);
lean_dec(v_a_3874_);
v___x_3879_ = l_Lean_Bool_toLBool(v___x_3878_);
v___x_3880_ = lean_box(v___x_3879_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v___x_3880_);
v___x_3882_ = v___x_3876_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3873_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3873_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3893_; lean_object* v_zero_3894_; uint8_t v_isZero_3895_; 
v_body_3893_ = lean_ctor_get(v_x_3859_, 2);
lean_inc_ref(v_body_3893_);
lean_dec_ref_known(v_x_3859_, 3);
v_zero_3894_ = lean_unsigned_to_nat(0u);
v_isZero_3895_ = lean_nat_dec_eq(v_x_3860_, v_zero_3894_);
if (v_isZero_3895_ == 1)
{
uint8_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec_ref(v_body_3893_);
lean_dec(v_x_3860_);
v___x_3896_ = 0;
v___x_3897_ = lean_box(v___x_3896_);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
else
{
lean_object* v_one_3899_; lean_object* v_n_3900_; 
v_one_3899_ = lean_unsigned_to_nat(1u);
v_n_3900_ = lean_nat_sub(v_x_3860_, v_one_3899_);
lean_dec(v_x_3860_);
v_x_3859_ = v_body_3893_;
v_x_3860_ = v_n_3900_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3902_; 
v_body_3902_ = lean_ctor_get(v_x_3859_, 3);
lean_inc_ref(v_body_3902_);
lean_dec_ref_known(v_x_3859_, 4);
v_x_3859_ = v_body_3902_;
goto _start;
}
case 10:
{
lean_object* v_expr_3904_; 
v_expr_3904_ = lean_ctor_get(v_x_3859_, 1);
lean_inc_ref(v_expr_3904_);
lean_dec_ref_known(v_x_3859_, 2);
v_x_3859_ = v_expr_3904_;
goto _start;
}
default: 
{
lean_dec(v_x_3860_);
lean_dec_ref(v_x_3859_);
goto v___jp_3866_;
}
}
v___jp_3866_:
{
uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = 2;
v___x_3868_ = lean_box(v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3906_, v_x_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3914_, lean_object* v_x_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
switch(lean_obj_tag(v_x_3914_))
{
case 4:
{
lean_object* v_declName_3921_; lean_object* v_us_3922_; lean_object* v___x_3923_; 
v_declName_3921_ = lean_ctor_get(v_x_3914_, 0);
lean_inc(v_declName_3921_);
v_us_3922_ = lean_ctor_get(v_x_3914_, 1);
lean_inc(v_us_3922_);
lean_dec_ref_known(v_x_3914_, 2);
v___x_3923_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3921_, v_us_3922_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3924_, v_x_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3925_;
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_x_3915_);
v_a_3926_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3923_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3923_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3934_; lean_object* v___x_3935_; 
v_fvarId_3934_ = lean_ctor_get(v_x_3914_, 0);
lean_inc(v_fvarId_3934_);
lean_dec_ref_known(v_x_3914_, 1);
v___x_3935_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3934_, v_a_3916_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3936_, v_x_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3937_;
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v_x_3915_);
v_a_3938_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3935_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3935_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3946_; lean_object* v___x_3947_; 
v_mvarId_3946_ = lean_ctor_get(v_x_3914_, 0);
lean_inc(v_mvarId_3946_);
lean_dec_ref_known(v_x_3914_, 1);
v___x_3947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3946_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
v___x_3949_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3948_, v_x_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3949_;
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec(v_x_3915_);
v_a_3950_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3947_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3947_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
case 5:
{
lean_object* v_fn_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_fn_3958_ = lean_ctor_get(v_x_3914_, 0);
lean_inc_ref(v_fn_3958_);
lean_dec_ref_known(v_x_3914_, 2);
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = lean_nat_add(v_x_3915_, v___x_3959_);
lean_dec(v_x_3915_);
v_x_3914_ = v_fn_3958_;
v_x_3915_ = v___x_3960_;
goto _start;
}
case 10:
{
lean_object* v_expr_3962_; 
v_expr_3962_ = lean_ctor_get(v_x_3914_, 1);
lean_inc_ref(v_expr_3962_);
lean_dec_ref_known(v_x_3914_, 2);
v_x_3914_ = v_expr_3962_;
goto _start;
}
case 8:
{
lean_object* v_body_3964_; 
v_body_3964_ = lean_ctor_get(v_x_3914_, 3);
lean_inc_ref(v_body_3964_);
lean_dec_ref_known(v_x_3914_, 4);
v_x_3914_ = v_body_3964_;
goto _start;
}
case 6:
{
lean_object* v_body_3966_; lean_object* v_zero_3967_; uint8_t v_isZero_3968_; 
v_body_3966_ = lean_ctor_get(v_x_3914_, 2);
lean_inc_ref(v_body_3966_);
lean_dec_ref_known(v_x_3914_, 3);
v_zero_3967_ = lean_unsigned_to_nat(0u);
v_isZero_3968_ = lean_nat_dec_eq(v_x_3915_, v_zero_3967_);
if (v_isZero_3968_ == 1)
{
uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref(v_body_3966_);
lean_dec(v_x_3915_);
v___x_3969_ = 0;
v___x_3970_ = lean_box(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
else
{
lean_object* v_one_3972_; lean_object* v_n_3973_; 
v_one_3972_ = lean_unsigned_to_nat(1u);
v_n_3973_ = lean_nat_sub(v_x_3915_, v_one_3972_);
lean_dec(v_x_3915_);
v_x_3914_ = v_body_3966_;
v_x_3915_ = v_n_3973_;
goto _start;
}
}
default: 
{
uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec(v_x_3915_);
lean_dec_ref(v_x_3914_);
v___x_3975_ = 2;
v___x_3976_ = lean_box(v___x_3975_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3978_, lean_object* v_x_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3978_, v_x_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
switch(lean_obj_tag(v_x_3986_))
{
case 0:
{
uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref_known(v_x_3986_, 1);
v___x_3992_ = 2;
v___x_3993_ = lean_box(v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
case 1:
{
lean_object* v_fvarId_3995_; lean_object* v___x_3996_; 
v_fvarId_3995_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_fvarId_3995_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_3996_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3995_, v_a_3987_, v_a_3989_, v_a_3990_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = lean_unsigned_to_nat(0u);
v___x_3999_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3997_, v___x_3998_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
return v___x_3999_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
v_a_4000_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3996_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3996_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4008_; lean_object* v___x_4009_; 
v_mvarId_4008_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_mvarId_4008_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_4009_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4008_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4011_ = lean_unsigned_to_nat(0u);
v___x_4012_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4010_, v___x_4011_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
return v___x_4012_;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4009_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4009_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
case 4:
{
lean_object* v_declName_4021_; lean_object* v_us_4022_; lean_object* v___x_4023_; 
v_declName_4021_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_declName_4021_);
v_us_4022_ = lean_ctor_get(v_x_3986_, 1);
lean_inc(v_us_4022_);
lean_dec_ref_known(v_x_3986_, 2);
v___x_4023_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4021_, v_us_4022_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = lean_unsigned_to_nat(0u);
v___x_4026_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4024_, v___x_4025_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
return v___x_4026_;
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
v_a_4027_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4023_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4023_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
case 5:
{
lean_object* v_fn_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_fn_4035_ = lean_ctor_get(v_x_3986_, 0);
lean_inc_ref(v_fn_4035_);
lean_dec_ref_known(v_x_3986_, 2);
v___x_4036_ = lean_unsigned_to_nat(1u);
v___x_4037_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4035_, v___x_4036_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
return v___x_4037_;
}
case 7:
{
lean_object* v_body_4038_; 
v_body_4038_ = lean_ctor_get(v_x_3986_, 2);
lean_inc_ref(v_body_4038_);
lean_dec_ref_known(v_x_3986_, 3);
v_x_3986_ = v_body_4038_;
goto _start;
}
case 8:
{
lean_object* v_body_4040_; 
v_body_4040_ = lean_ctor_get(v_x_3986_, 3);
lean_inc_ref(v_body_4040_);
lean_dec_ref_known(v_x_3986_, 4);
v_x_3986_ = v_body_4040_;
goto _start;
}
case 10:
{
lean_object* v_expr_4042_; 
v_expr_4042_ = lean_ctor_get(v_x_3986_, 1);
lean_inc_ref(v_expr_4042_);
lean_dec_ref_known(v_x_3986_, 2);
v_x_3986_ = v_expr_4042_;
goto _start;
}
case 11:
{
uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_dec_ref_known(v_x_3986_, 3);
v___x_4044_ = 2;
v___x_4045_ = lean_box(v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
default: 
{
uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec_ref(v_x_3986_);
v___x_4047_ = 0;
v___x_4048_ = lean_box(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Meta_isPropQuick(v_x_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v___x_4063_; 
lean_inc_ref(v_e_4057_);
v___x_4063_ = l_Lean_Meta_isPropQuick(v_e_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4120_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4120_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4120_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
uint8_t v___x_4068_; 
v___x_4068_ = lean_unbox(v_a_4064_);
lean_dec(v_a_4064_);
switch(v___x_4068_)
{
case 0:
{
uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
lean_dec_ref(v_e_4057_);
v___x_4069_ = 0;
v___x_4070_ = lean_box(v___x_4069_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4070_);
v___x_4072_ = v___x_4066_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
case 1:
{
uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
lean_dec_ref(v_e_4057_);
v___x_4074_ = 1;
v___x_4075_ = lean_box(v___x_4074_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4075_);
v___x_4077_ = v___x_4066_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
default: 
{
lean_object* v___x_4079_; 
lean_del_object(v___x_4066_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
v___x_4079_ = lean_infer_type(v_e_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = l_Lean_Meta_whnfD(v_a_4080_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4103_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4103_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4103_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
if (lean_obj_tag(v_a_4082_) == 3)
{
lean_object* v_u_4086_; lean_object* v___x_4087_; lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4097_; 
lean_del_object(v___x_4084_);
v_u_4086_ = lean_ctor_get(v_a_4082_, 0);
lean_inc(v_u_4086_);
lean_dec_ref_known(v_a_4082_, 1);
v___x_4087_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4086_, v_a_4059_);
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4097_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4097_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
uint8_t v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4092_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4088_);
lean_dec(v_a_4088_);
v___x_4093_ = lean_box(v___x_4092_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4093_);
v___x_4095_ = v___x_4090_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
else
{
uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec(v_a_4082_);
v___x_4098_ = 0;
v___x_4099_ = lean_box(v___x_4098_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4099_);
v___x_4101_ = v___x_4084_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
v_a_4104_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4081_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4081_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
v_a_4112_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4079_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4079_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
lean_dec_ref(v_e_4057_);
v_a_4121_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4063_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4063_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_Meta_isProp(v_e_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4136_){
_start:
{
switch(lean_obj_tag(v_x_4136_))
{
case 0:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_unsigned_to_nat(0u);
return v___x_4137_;
}
case 1:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_unsigned_to_nat(1u);
return v___x_4138_;
}
case 2:
{
lean_object* v___x_4139_; 
v___x_4139_ = lean_unsigned_to_nat(2u);
return v___x_4139_;
}
default: 
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_unsigned_to_nat(3u);
return v___x_4140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4141_);
lean_dec(v_x_4141_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4143_, lean_object* v_k_4144_){
_start:
{
if (lean_obj_tag(v_t_4143_) == 3)
{
lean_object* v_idx_4145_; lean_object* v___x_4146_; 
v_idx_4145_ = lean_ctor_get(v_t_4143_, 0);
lean_inc(v_idx_4145_);
lean_dec_ref_known(v_t_4143_, 1);
v___x_4146_ = lean_apply_1(v_k_4144_, v_idx_4145_);
return v___x_4146_;
}
else
{
lean_dec(v_t_4143_);
return v_k_4144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4147_, lean_object* v_ctorIdx_4148_, lean_object* v_t_4149_, lean_object* v_h_4150_, lean_object* v_k_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4149_, v_k_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4153_, lean_object* v_ctorIdx_4154_, lean_object* v_t_4155_, lean_object* v_h_4156_, lean_object* v_k_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4153_, v_ctorIdx_4154_, v_t_4155_, v_h_4156_, v_k_4157_);
lean_dec(v_ctorIdx_4154_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4159_, lean_object* v_false_4160_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4159_, v_false_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4162_, lean_object* v_t_4163_, lean_object* v_h_4164_, lean_object* v_false_4165_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4163_, v_false_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4167_, lean_object* v_true_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4167_, v_true_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4170_, lean_object* v_t_4171_, lean_object* v_h_4172_, lean_object* v_true_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4171_, v_true_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4175_, lean_object* v_undef_4176_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4175_, v_undef_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4178_, lean_object* v_t_4179_, lean_object* v_h_4180_, lean_object* v_undef_4181_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4179_, v_undef_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4183_, lean_object* v_bvar_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4183_, v_bvar_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4186_, lean_object* v_t_4187_, lean_object* v_h_4188_, lean_object* v_bvar_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4187_, v_bvar_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4191_){
_start:
{
switch(v_x_4191_)
{
case 0:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_box(0);
return v___x_4192_;
}
case 1:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_box(1);
return v___x_4193_;
}
default: 
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_box(2);
return v___x_4194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4195_){
_start:
{
uint8_t v_x_25__boxed_4196_; lean_object* v_res_4197_; 
v_x_25__boxed_4196_ = lean_unbox(v_x_4195_);
v_res_4197_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4196_);
return v_res_4197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4198_){
_start:
{
switch(lean_obj_tag(v_x_4198_))
{
case 0:
{
uint8_t v___x_4199_; 
v___x_4199_ = 0;
return v___x_4199_;
}
case 1:
{
uint8_t v___x_4200_; 
v___x_4200_ = 1;
return v___x_4200_;
}
default: 
{
uint8_t v___x_4201_; 
v___x_4201_ = 2;
return v___x_4201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4202_){
_start:
{
uint8_t v_res_4203_; lean_object* v_r_4204_; 
v_res_4203_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4202_);
lean_dec(v_x_4202_);
v_r_4204_ = lean_box(v_res_4203_);
return v_r_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4206_){
_start:
{
switch(lean_obj_tag(v_e_4206_))
{
case 3:
{
lean_object* v_u_4207_; uint8_t v___x_4208_; 
v_u_4207_ = lean_ctor_get(v_e_4206_, 0);
v___x_4208_ = l_Lean_Level_isNeverZero(v_u_4207_);
if (v___x_4208_ == 0)
{
uint8_t v___x_4209_; 
v___x_4209_ = l_Lean_Level_isZero(v_u_4207_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_box(2);
return v___x_4210_;
}
else
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_box(1);
return v___x_4211_;
}
}
else
{
lean_object* v___x_4212_; 
v___x_4212_ = lean_box(0);
return v___x_4212_;
}
}
case 5:
{
lean_object* v_fn_4213_; 
v_fn_4213_ = lean_ctor_get(v_e_4206_, 0);
if (lean_obj_tag(v_fn_4213_) == 4)
{
lean_object* v_declName_4214_; 
v_declName_4214_ = lean_ctor_get(v_fn_4213_, 0);
if (lean_obj_tag(v_declName_4214_) == 1)
{
lean_object* v_pre_4215_; 
v_pre_4215_ = lean_ctor_get(v_declName_4214_, 0);
if (lean_obj_tag(v_pre_4215_) == 0)
{
lean_object* v_arg_4216_; lean_object* v_str_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v_arg_4216_ = lean_ctor_get(v_e_4206_, 1);
v_str_4217_ = lean_ctor_get(v_declName_4214_, 1);
v___x_4218_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4219_ = lean_string_dec_eq(v_str_4217_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_box(2);
return v___x_4220_;
}
else
{
v_e_4206_ = v_arg_4216_;
goto _start;
}
}
else
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_box(2);
return v___x_4222_;
}
}
else
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(2);
return v___x_4223_;
}
}
else
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_box(2);
return v___x_4224_;
}
}
default: 
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_box(2);
return v___x_4225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4226_);
lean_dec_ref(v_e_4226_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4228_, lean_object* v_binderType_4229_){
_start:
{
if (lean_obj_tag(v_r_4228_) == 3)
{
lean_object* v_idx_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4242_; 
v_idx_4230_ = lean_ctor_get(v_r_4228_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_r_4228_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4232_ = v_r_4228_;
v_isShared_4233_ = v_isSharedCheck_4242_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_idx_4230_);
lean_dec(v_r_4228_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4242_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v_zero_4234_; uint8_t v_isZero_4235_; 
v_zero_4234_ = lean_unsigned_to_nat(0u);
v_isZero_4235_ = lean_nat_dec_eq(v_idx_4230_, v_zero_4234_);
if (v_isZero_4235_ == 1)
{
lean_object* v___x_4236_; 
lean_del_object(v___x_4232_);
lean_dec(v_idx_4230_);
v___x_4236_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4229_);
return v___x_4236_;
}
else
{
lean_object* v_one_4237_; lean_object* v_n_4238_; lean_object* v___x_4240_; 
v_one_4237_ = lean_unsigned_to_nat(1u);
v_n_4238_ = lean_nat_sub(v_idx_4230_, v_one_4237_);
lean_dec(v_idx_4230_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v_n_4238_);
v___x_4240_ = v___x_4232_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_n_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
return v_r_4228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4243_, lean_object* v_binderType_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4243_, v_binderType_4244_);
lean_dec_ref(v_binderType_4244_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4246_, lean_object* v_x_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_type_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; 
switch(lean_obj_tag(v_x_4246_))
{
case 7:
{
lean_object* v_binderType_4281_; lean_object* v_body_4282_; lean_object* v_zero_4283_; uint8_t v_isZero_4284_; 
v_binderType_4281_ = lean_ctor_get(v_x_4246_, 1);
v_body_4282_ = lean_ctor_get(v_x_4246_, 2);
v_zero_4283_ = lean_unsigned_to_nat(0u);
v_isZero_4284_ = lean_nat_dec_eq(v_x_4247_, v_zero_4283_);
if (v_isZero_4284_ == 1)
{
v_type_4254_ = v_x_4246_;
v___y_4255_ = v_a_4248_;
v___y_4256_ = v_a_4249_;
v___y_4257_ = v_a_4250_;
v___y_4258_ = v_a_4251_;
goto v___jp_4253_;
}
else
{
lean_object* v_one_4285_; lean_object* v_n_4286_; lean_object* v___x_4287_; 
lean_inc_ref(v_body_4282_);
lean_inc_ref(v_binderType_4281_);
lean_dec_ref_known(v_x_4246_, 3);
v_one_4285_ = lean_unsigned_to_nat(1u);
v_n_4286_ = lean_nat_sub(v_x_4247_, v_one_4285_);
v___x_4287_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4282_, v_n_4286_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
lean_dec(v_n_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4296_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4296_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4296_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4294_; 
v___x_4292_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4288_, v_binderType_4281_);
lean_dec_ref(v_binderType_4281_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4292_);
v___x_4294_ = v___x_4290_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4292_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
else
{
lean_dec_ref(v_binderType_4281_);
return v___x_4287_;
}
}
}
case 8:
{
lean_object* v_type_4297_; lean_object* v_body_4298_; lean_object* v___x_4299_; 
v_type_4297_ = lean_ctor_get(v_x_4246_, 1);
lean_inc_ref(v_type_4297_);
v_body_4298_ = lean_ctor_get(v_x_4246_, 3);
lean_inc_ref(v_body_4298_);
lean_dec_ref_known(v_x_4246_, 4);
v___x_4299_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4298_, v_x_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4308_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4308_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4304_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4300_, v_type_4297_);
lean_dec_ref(v_type_4297_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4304_);
v___x_4306_ = v___x_4302_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
else
{
lean_dec_ref(v_type_4297_);
return v___x_4299_;
}
}
case 10:
{
lean_object* v_expr_4309_; 
v_expr_4309_ = lean_ctor_get(v_x_4246_, 1);
lean_inc_ref(v_expr_4309_);
lean_dec_ref_known(v_x_4246_, 2);
v_x_4246_ = v_expr_4309_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v_deBruijnIndex_4311_ = lean_ctor_get(v_x_4246_, 0);
lean_inc(v_deBruijnIndex_4311_);
lean_dec_ref_known(v_x_4246_, 1);
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_nat_dec_eq(v_x_4247_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_dec(v_deBruijnIndex_4311_);
goto v___jp_4278_;
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4314_, 0, v_deBruijnIndex_4311_);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
default: 
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_nat_dec_eq(v_x_4247_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_dec_ref(v_x_4246_);
goto v___jp_4278_;
}
else
{
v_type_4254_ = v_x_4246_;
v___y_4255_ = v_a_4248_;
v___y_4256_ = v_a_4249_;
v___y_4257_ = v_a_4250_;
v___y_4258_ = v_a_4251_;
goto v___jp_4253_;
}
}
}
v___jp_4253_:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_Meta_isPropQuick(v_type_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4269_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4269_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4269_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
uint8_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4264_ = lean_unbox(v_a_4260_);
lean_dec(v_a_4260_);
v___x_4265_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4264_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4265_);
v___x_4267_ = v___x_4262_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_a_4270_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4259_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4259_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
v___jp_4278_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = lean_box(2);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4318_, lean_object* v_x_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4318_, v_x_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_x_4319_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4326_, lean_object* v_n_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4326_, v_n_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4343_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4343_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4343_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4341_; 
v___x_4338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4334_);
lean_dec(v_a_4334_);
v___x_4339_ = lean_box(v___x_4338_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v___x_4339_);
v___x_4341_ = v___x_4336_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
v_a_4344_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4333_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4333_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4352_, lean_object* v_n_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4352_, v_n_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_n_4353_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4360_, lean_object* v_x_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
switch(lean_obj_tag(v_x_4360_))
{
case 4:
{
lean_object* v_declName_4367_; lean_object* v_us_4368_; lean_object* v___x_4369_; 
v_declName_4367_ = lean_ctor_get(v_x_4360_, 0);
lean_inc(v_declName_4367_);
v_us_4368_ = lean_ctor_get(v_x_4360_, 1);
lean_inc(v_us_4368_);
lean_dec_ref_known(v_x_4360_, 2);
v___x_4369_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4367_, v_us_4368_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4370_, v_x_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_x_4361_);
return v___x_4371_;
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_x_4361_);
v_a_4372_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4369_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4369_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4380_; lean_object* v___x_4381_; 
v_fvarId_4380_ = lean_ctor_get(v_x_4360_, 0);
lean_inc(v_fvarId_4380_);
lean_dec_ref_known(v_x_4360_, 1);
v___x_4381_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4380_, v_a_4362_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4383_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v___x_4383_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4382_, v_x_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_x_4361_);
return v___x_4383_;
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
lean_dec(v_x_4361_);
v_a_4384_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4381_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4381_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4392_; lean_object* v___x_4393_; 
v_mvarId_4392_ = lean_ctor_get(v_x_4360_, 0);
lean_inc(v_mvarId_4392_);
lean_dec_ref_known(v_x_4360_, 1);
v___x_4393_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4392_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4394_, v_x_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_x_4361_);
return v___x_4395_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_x_4361_);
v_a_4396_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4393_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4393_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
case 5:
{
lean_object* v_fn_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_fn_4404_ = lean_ctor_get(v_x_4360_, 0);
lean_inc_ref(v_fn_4404_);
lean_dec_ref_known(v_x_4360_, 2);
v___x_4405_ = lean_unsigned_to_nat(1u);
v___x_4406_ = lean_nat_add(v_x_4361_, v___x_4405_);
lean_dec(v_x_4361_);
v_x_4360_ = v_fn_4404_;
v_x_4361_ = v___x_4406_;
goto _start;
}
case 10:
{
lean_object* v_expr_4408_; 
v_expr_4408_ = lean_ctor_get(v_x_4360_, 1);
lean_inc_ref(v_expr_4408_);
lean_dec_ref_known(v_x_4360_, 2);
v_x_4360_ = v_expr_4408_;
goto _start;
}
case 8:
{
lean_object* v_body_4410_; 
v_body_4410_ = lean_ctor_get(v_x_4360_, 3);
lean_inc_ref(v_body_4410_);
lean_dec_ref_known(v_x_4360_, 4);
v_x_4360_ = v_body_4410_;
goto _start;
}
case 6:
{
lean_object* v_body_4412_; lean_object* v_zero_4413_; uint8_t v_isZero_4414_; 
v_body_4412_ = lean_ctor_get(v_x_4360_, 2);
lean_inc_ref(v_body_4412_);
lean_dec_ref_known(v_x_4360_, 3);
v_zero_4413_ = lean_unsigned_to_nat(0u);
v_isZero_4414_ = lean_nat_dec_eq(v_x_4361_, v_zero_4413_);
if (v_isZero_4414_ == 1)
{
lean_object* v___x_4415_; 
lean_dec(v_x_4361_);
v___x_4415_ = l_Lean_Meta_isProofQuick(v_body_4412_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
return v___x_4415_;
}
else
{
lean_object* v_one_4416_; lean_object* v_n_4417_; 
v_one_4416_ = lean_unsigned_to_nat(1u);
v_n_4417_ = lean_nat_sub(v_x_4361_, v_one_4416_);
lean_dec(v_x_4361_);
v_x_4360_ = v_body_4412_;
v_x_4361_ = v_n_4417_;
goto _start;
}
}
default: 
{
uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_dec(v_x_4361_);
lean_dec_ref(v_x_4360_);
v___x_4419_ = 2;
v___x_4420_ = lean_box(v___x_4419_);
v___x_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
return v___x_4421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
switch(lean_obj_tag(v_x_4422_))
{
case 0:
{
uint8_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref_known(v_x_4422_, 1);
v___x_4428_ = 2;
v___x_4429_ = lean_box(v___x_4428_);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
case 1:
{
lean_object* v_fvarId_4431_; lean_object* v___x_4432_; 
v_fvarId_4431_ = lean_ctor_get(v_x_4422_, 0);
lean_inc(v_fvarId_4431_);
lean_dec_ref_known(v_x_4422_, 1);
v___x_4432_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4431_, v_a_4423_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4432_, 1);
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4433_, v___x_4434_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
return v___x_4435_;
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
v_a_4436_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4432_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4432_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4444_; lean_object* v___x_4445_; 
v_mvarId_4444_ = lean_ctor_get(v_x_4422_, 0);
lean_inc(v_mvarId_4444_);
lean_dec_ref_known(v_x_4422_, 1);
v___x_4445_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4444_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref_known(v___x_4445_, 1);
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4446_, v___x_4447_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
return v___x_4448_;
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
v_a_4449_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4445_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4445_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
case 4:
{
lean_object* v_declName_4457_; lean_object* v_us_4458_; lean_object* v___x_4459_; 
v_declName_4457_ = lean_ctor_get(v_x_4422_, 0);
lean_inc(v_declName_4457_);
v_us_4458_ = lean_ctor_get(v_x_4422_, 1);
lean_inc(v_us_4458_);
lean_dec_ref_known(v_x_4422_, 2);
v___x_4459_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4457_, v_us_4458_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4460_, v___x_4461_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
v_a_4463_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4459_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4459_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
case 5:
{
lean_object* v_fn_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v_fn_4471_ = lean_ctor_get(v_x_4422_, 0);
lean_inc_ref(v_fn_4471_);
lean_dec_ref_known(v_x_4422_, 2);
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4471_, v___x_4472_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
return v___x_4473_;
}
case 6:
{
lean_object* v_body_4474_; 
v_body_4474_ = lean_ctor_get(v_x_4422_, 2);
lean_inc_ref(v_body_4474_);
lean_dec_ref_known(v_x_4422_, 3);
v_x_4422_ = v_body_4474_;
goto _start;
}
case 8:
{
lean_object* v_body_4476_; 
v_body_4476_ = lean_ctor_get(v_x_4422_, 3);
lean_inc_ref(v_body_4476_);
lean_dec_ref_known(v_x_4422_, 4);
v_x_4422_ = v_body_4476_;
goto _start;
}
case 10:
{
lean_object* v_expr_4478_; 
v_expr_4478_ = lean_ctor_get(v_x_4422_, 1);
lean_inc_ref(v_expr_4478_);
lean_dec_ref_known(v_x_4422_, 2);
v_x_4422_ = v_expr_4478_;
goto _start;
}
case 11:
{
uint8_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_dec_ref_known(v_x_4422_, 3);
v___x_4480_ = 2;
v___x_4481_ = lean_box(v___x_4480_);
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
return v___x_4482_;
}
default: 
{
uint8_t v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
lean_dec_ref(v_x_4422_);
v___x_4483_ = 0;
v___x_4484_ = lean_box(v___x_4483_);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
return v___x_4485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_Meta_isProofQuick(v_x_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4493_, lean_object* v_x_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4493_, v_x_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v___x_4507_; 
lean_inc_ref(v_e_4501_);
v___x_4507_ = l_Lean_Meta_isProofQuick(v_e_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4534_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4534_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4534_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
uint8_t v___x_4512_; 
v___x_4512_ = lean_unbox(v_a_4508_);
lean_dec(v_a_4508_);
switch(v___x_4512_)
{
case 0:
{
uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4516_; 
lean_dec_ref(v_e_4501_);
v___x_4513_ = 0;
v___x_4514_ = lean_box(v___x_4513_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4514_);
v___x_4516_ = v___x_4510_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
case 1:
{
uint8_t v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
lean_dec_ref(v_e_4501_);
v___x_4518_ = 1;
v___x_4519_ = lean_box(v___x_4518_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4519_);
v___x_4521_ = v___x_4510_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
default: 
{
lean_object* v___x_4523_; 
lean_del_object(v___x_4510_);
lean_inc(v_a_4505_);
lean_inc_ref(v_a_4504_);
lean_inc(v_a_4503_);
lean_inc_ref(v_a_4502_);
v___x_4523_ = lean_infer_type(v_e_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v___x_4525_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v___x_4523_, 1);
v___x_4525_ = l_Lean_Meta_isProp(v_a_4524_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
return v___x_4525_;
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
v_a_4526_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4523_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4523_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_dec_ref(v_e_4501_);
v_a_4535_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4507_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4507_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Meta_isProof(v_e_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4550_, lean_object* v_x_4551_){
_start:
{
switch(lean_obj_tag(v_x_4550_))
{
case 3:
{
lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = lean_nat_dec_eq(v_x_4551_, v___x_4557_);
lean_dec(v_x_4551_);
if (v___x_4558_ == 0)
{
goto v___jp_4553_;
}
else
{
uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = 1;
v___x_4560_ = lean_box(v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
}
case 7:
{
lean_object* v_body_4562_; lean_object* v_zero_4563_; uint8_t v_isZero_4564_; 
v_body_4562_ = lean_ctor_get(v_x_4550_, 2);
v_zero_4563_ = lean_unsigned_to_nat(0u);
v_isZero_4564_ = lean_nat_dec_eq(v_x_4551_, v_zero_4563_);
if (v_isZero_4564_ == 1)
{
uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
lean_dec(v_x_4551_);
v___x_4565_ = 0;
v___x_4566_ = lean_box(v___x_4565_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
else
{
lean_object* v_one_4568_; lean_object* v_n_4569_; 
v_one_4568_ = lean_unsigned_to_nat(1u);
v_n_4569_ = lean_nat_sub(v_x_4551_, v_one_4568_);
lean_dec(v_x_4551_);
v_x_4550_ = v_body_4562_;
v_x_4551_ = v_n_4569_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4571_; 
v_body_4571_ = lean_ctor_get(v_x_4550_, 3);
v_x_4550_ = v_body_4571_;
goto _start;
}
case 10:
{
lean_object* v_expr_4573_; 
v_expr_4573_ = lean_ctor_get(v_x_4550_, 1);
v_x_4550_ = v_expr_4573_;
goto _start;
}
default: 
{
lean_dec(v_x_4551_);
goto v___jp_4553_;
}
}
v___jp_4553_:
{
uint8_t v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = 2;
v___x_4555_ = lean_box(v___x_4554_);
v___x_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
return v___x_4556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4575_, lean_object* v_x_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4575_, v_x_4576_);
lean_dec_ref(v_x_4575_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4579_, lean_object* v_x_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4579_, v_x_4580_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4587_, lean_object* v_x_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4587_, v_x_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec_ref(v_x_4587_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4595_, lean_object* v_x_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
switch(lean_obj_tag(v_x_4595_))
{
case 4:
{
lean_object* v_declName_4602_; lean_object* v_us_4603_; lean_object* v___x_4604_; 
v_declName_4602_ = lean_ctor_get(v_x_4595_, 0);
lean_inc(v_declName_4602_);
v_us_4603_ = lean_ctor_get(v_x_4595_, 1);
lean_inc(v_us_4603_);
lean_dec_ref_known(v_x_4595_, 2);
v___x_4604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4602_, v_us_4603_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4606_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
v___x_4606_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4605_, v_x_4596_);
lean_dec(v_a_4605_);
return v___x_4606_;
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec(v_x_4596_);
v_a_4607_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4604_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4604_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4615_; lean_object* v___x_4616_; 
v_fvarId_4615_ = lean_ctor_get(v_x_4595_, 0);
lean_inc(v_fvarId_4615_);
lean_dec_ref_known(v_x_4595_, 1);
v___x_4616_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4615_, v_a_4597_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4618_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v___x_4616_, 1);
v___x_4618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4617_, v_x_4596_);
lean_dec(v_a_4617_);
return v___x_4618_;
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_dec(v_x_4596_);
v_a_4619_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4616_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4616_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4627_; lean_object* v___x_4628_; 
v_mvarId_4627_ = lean_ctor_get(v_x_4595_, 0);
lean_inc(v_mvarId_4627_);
lean_dec_ref_known(v_x_4595_, 1);
v___x_4628_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4627_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v___x_4630_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4629_, v_x_4596_);
lean_dec(v_a_4629_);
return v___x_4630_;
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec(v_x_4596_);
v_a_4631_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4628_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4628_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
case 5:
{
lean_object* v_fn_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v_fn_4639_ = lean_ctor_get(v_x_4595_, 0);
lean_inc_ref(v_fn_4639_);
lean_dec_ref_known(v_x_4595_, 2);
v___x_4640_ = lean_unsigned_to_nat(1u);
v___x_4641_ = lean_nat_add(v_x_4596_, v___x_4640_);
lean_dec(v_x_4596_);
v_x_4595_ = v_fn_4639_;
v_x_4596_ = v___x_4641_;
goto _start;
}
case 10:
{
lean_object* v_expr_4643_; 
v_expr_4643_ = lean_ctor_get(v_x_4595_, 1);
lean_inc_ref(v_expr_4643_);
lean_dec_ref_known(v_x_4595_, 2);
v_x_4595_ = v_expr_4643_;
goto _start;
}
case 8:
{
lean_object* v_body_4645_; 
v_body_4645_ = lean_ctor_get(v_x_4595_, 3);
lean_inc_ref(v_body_4645_);
lean_dec_ref_known(v_x_4595_, 4);
v_x_4595_ = v_body_4645_;
goto _start;
}
case 6:
{
lean_object* v_body_4647_; lean_object* v_zero_4648_; uint8_t v_isZero_4649_; 
v_body_4647_ = lean_ctor_get(v_x_4595_, 2);
lean_inc_ref(v_body_4647_);
lean_dec_ref_known(v_x_4595_, 3);
v_zero_4648_ = lean_unsigned_to_nat(0u);
v_isZero_4649_ = lean_nat_dec_eq(v_x_4596_, v_zero_4648_);
if (v_isZero_4649_ == 1)
{
uint8_t v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
lean_dec_ref(v_body_4647_);
lean_dec(v_x_4596_);
v___x_4650_ = 0;
v___x_4651_ = lean_box(v___x_4650_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
else
{
lean_object* v_one_4653_; lean_object* v_n_4654_; 
v_one_4653_ = lean_unsigned_to_nat(1u);
v_n_4654_ = lean_nat_sub(v_x_4596_, v_one_4653_);
lean_dec(v_x_4596_);
v_x_4595_ = v_body_4647_;
v_x_4596_ = v_n_4654_;
goto _start;
}
}
default: 
{
uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
lean_dec(v_x_4596_);
lean_dec_ref(v_x_4595_);
v___x_4656_ = 2;
v___x_4657_ = lean_box(v___x_4656_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4659_, lean_object* v_x_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4659_, v_x_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
switch(lean_obj_tag(v_x_4667_))
{
case 1:
{
lean_object* v_fvarId_4673_; lean_object* v___x_4674_; 
v_fvarId_4673_ = lean_ctor_get(v_x_4667_, 0);
lean_inc(v_fvarId_4673_);
lean_dec_ref_known(v_x_4667_, 1);
v___x_4674_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4673_, v_a_4668_, v_a_4670_, v_a_4671_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = lean_unsigned_to_nat(0u);
v___x_4677_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4675_, v___x_4676_);
lean_dec(v_a_4675_);
return v___x_4677_;
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
v_a_4678_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4674_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4674_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4686_; lean_object* v___x_4687_; 
v_mvarId_4686_ = lean_ctor_get(v_x_4667_, 0);
lean_inc(v_mvarId_4686_);
lean_dec_ref_known(v_x_4667_, 1);
v___x_4687_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4686_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
v___x_4689_ = lean_unsigned_to_nat(0u);
v___x_4690_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4688_, v___x_4689_);
lean_dec(v_a_4688_);
return v___x_4690_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
v_a_4691_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4687_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4687_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
case 3:
{
uint8_t v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
lean_dec_ref_known(v_x_4667_, 1);
v___x_4699_ = 1;
v___x_4700_ = lean_box(v___x_4699_);
v___x_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4701_, 0, v___x_4700_);
return v___x_4701_;
}
case 4:
{
lean_object* v_declName_4702_; lean_object* v_us_4703_; lean_object* v___x_4704_; 
v_declName_4702_ = lean_ctor_get(v_x_4667_, 0);
lean_inc(v_declName_4702_);
v_us_4703_ = lean_ctor_get(v_x_4667_, 1);
lean_inc(v_us_4703_);
lean_dec_ref_known(v_x_4667_, 2);
v___x_4704_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4702_, v_us_4703_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref_known(v___x_4704_, 1);
v___x_4706_ = lean_unsigned_to_nat(0u);
v___x_4707_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4705_, v___x_4706_);
lean_dec(v_a_4705_);
return v___x_4707_;
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4704_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4704_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
case 5:
{
lean_object* v_fn_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_fn_4716_ = lean_ctor_get(v_x_4667_, 0);
lean_inc_ref(v_fn_4716_);
lean_dec_ref_known(v_x_4667_, 2);
v___x_4717_ = lean_unsigned_to_nat(1u);
v___x_4718_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4716_, v___x_4717_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
return v___x_4718_;
}
case 6:
{
uint8_t v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_dec_ref_known(v_x_4667_, 3);
v___x_4719_ = 0;
v___x_4720_ = lean_box(v___x_4719_);
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
case 7:
{
uint8_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
lean_dec_ref_known(v_x_4667_, 3);
v___x_4722_ = 1;
v___x_4723_ = lean_box(v___x_4722_);
v___x_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4723_);
return v___x_4724_;
}
case 8:
{
lean_object* v_body_4725_; 
v_body_4725_ = lean_ctor_get(v_x_4667_, 3);
lean_inc_ref(v_body_4725_);
lean_dec_ref_known(v_x_4667_, 4);
v_x_4667_ = v_body_4725_;
goto _start;
}
case 9:
{
uint8_t v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_dec_ref_known(v_x_4667_, 1);
v___x_4727_ = 0;
v___x_4728_ = lean_box(v___x_4727_);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
return v___x_4729_;
}
case 10:
{
lean_object* v_expr_4730_; 
v_expr_4730_ = lean_ctor_get(v_x_4667_, 1);
lean_inc_ref(v_expr_4730_);
lean_dec_ref_known(v_x_4667_, 2);
v_x_4667_ = v_expr_4730_;
goto _start;
}
default: 
{
uint8_t v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
lean_dec_ref(v_x_4667_);
v___x_4732_ = 2;
v___x_4733_ = lean_box(v___x_4732_);
v___x_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
return v___x_4734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_Meta_isTypeQuick(v_x_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v___x_4748_; 
lean_inc_ref(v_e_4742_);
v___x_4748_ = l_Lean_Meta_isTypeQuick(v_e_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4798_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4798_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4798_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
uint8_t v___x_4753_; 
v___x_4753_ = lean_unbox(v_a_4749_);
lean_dec(v_a_4749_);
switch(v___x_4753_)
{
case 0:
{
uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
lean_dec_ref(v_e_4742_);
v___x_4754_ = 0;
v___x_4755_ = lean_box(v___x_4754_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4755_);
v___x_4757_ = v___x_4751_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
case 1:
{
uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
lean_dec_ref(v_e_4742_);
v___x_4759_ = 1;
v___x_4760_ = lean_box(v___x_4759_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4760_);
v___x_4762_ = v___x_4751_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
default: 
{
lean_object* v___x_4764_; 
lean_del_object(v___x_4751_);
lean_inc(v_a_4746_);
lean_inc_ref(v_a_4745_);
lean_inc(v_a_4744_);
lean_inc_ref(v_a_4743_);
v___x_4764_ = lean_infer_type(v_e_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = l_Lean_Meta_whnfD(v_a_4765_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4781_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4781_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4781_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
if (lean_obj_tag(v_a_4767_) == 3)
{
uint8_t v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
lean_dec_ref_known(v_a_4767_, 1);
v___x_4771_ = 1;
v___x_4772_ = lean_box(v___x_4771_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4772_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
else
{
uint8_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
lean_dec(v_a_4767_);
v___x_4776_ = 0;
v___x_4777_ = lean_box(v___x_4776_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4777_);
v___x_4779_ = v___x_4769_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
v_a_4782_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4766_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4766_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
v_a_4790_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4764_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4764_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec_ref(v_e_4742_);
v_a_4799_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4748_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4748_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_Meta_isType(v_e_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4814_){
_start:
{
switch(lean_obj_tag(v_x_4814_))
{
case 7:
{
lean_object* v_body_4815_; 
v_body_4815_ = lean_ctor_get(v_x_4814_, 2);
v_x_4814_ = v_body_4815_;
goto _start;
}
case 3:
{
lean_object* v_u_4817_; lean_object* v___x_4818_; 
v_u_4817_ = lean_ctor_get(v_x_4814_, 0);
lean_inc(v_u_4817_);
v___x_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4818_, 0, v_u_4817_);
return v___x_4818_;
}
default: 
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_box(0);
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4820_);
lean_dec_ref(v_x_4820_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4822_, lean_object* v_body_4823_, lean_object* v_x_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4822_, v_body_4823_, v_x_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4833_, lean_object* v_xs_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
switch(lean_obj_tag(v_type_4833_))
{
case 3:
{
lean_object* v_u_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec_ref(v_xs_4834_);
v_u_4840_ = lean_ctor_get(v_type_4833_, 0);
lean_inc(v_u_4840_);
lean_dec_ref_known(v_type_4833_, 1);
v___x_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4841_, 0, v_u_4840_);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
return v___x_4842_;
}
case 7:
{
lean_object* v_binderName_4843_; lean_object* v_binderType_4844_; lean_object* v_body_4845_; uint8_t v_binderInfo_4846_; lean_object* v___f_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v_binderName_4843_ = lean_ctor_get(v_type_4833_, 0);
lean_inc(v_binderName_4843_);
v_binderType_4844_ = lean_ctor_get(v_type_4833_, 1);
lean_inc_ref(v_binderType_4844_);
v_body_4845_ = lean_ctor_get(v_type_4833_, 2);
lean_inc_ref(v_body_4845_);
v_binderInfo_4846_ = lean_ctor_get_uint8(v_type_4833_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4833_, 3);
lean_inc_ref(v_xs_4834_);
v___f_4847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4847_, 0, v_xs_4834_);
lean_closure_set(v___f_4847_, 1, v_body_4845_);
v___x_4848_ = lean_expr_instantiate_rev(v_binderType_4844_, v_xs_4834_);
lean_dec_ref(v_xs_4834_);
lean_dec_ref(v_binderType_4844_);
v___x_4849_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4843_, v_binderInfo_4846_, v___x_4848_, v___f_4847_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
return v___x_4849_;
}
default: 
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4850_ = lean_expr_instantiate_rev(v_type_4833_, v_xs_4834_);
lean_dec_ref(v_xs_4834_);
lean_dec_ref(v_type_4833_);
v___x_4851_ = l_Lean_Meta_whnfD(v___x_4850_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4867_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4867_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4867_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
switch(lean_obj_tag(v_a_4852_))
{
case 3:
{
lean_object* v_u_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
v_u_4856_ = lean_ctor_get(v_a_4852_, 0);
lean_inc(v_u_4856_);
lean_dec_ref_known(v_a_4852_, 1);
v___x_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4857_, 0, v_u_4856_);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4857_);
v___x_4859_ = v___x_4854_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4857_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
case 7:
{
lean_object* v___x_4861_; 
lean_del_object(v___x_4854_);
v___x_4861_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4833_ = v_a_4852_;
v_xs_4834_ = v___x_4861_;
goto _start;
}
default: 
{
lean_object* v___x_4863_; lean_object* v___x_4865_; 
lean_dec(v_a_4852_);
v___x_4863_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4863_);
v___x_4865_ = v___x_4854_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4851_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4851_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4876_, lean_object* v_body_4877_, lean_object* v_x_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_array_push(v_xs_4876_, v_x_4878_);
v___x_4885_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4877_, v___x_4884_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4886_, lean_object* v_xs_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4886_, v_xs_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4894_, lean_object* v_cache_4895_, lean_object* v_a_x3f_4896_){
_start:
{
lean_object* v___x_4898_; lean_object* v_mctx_4899_; lean_object* v_zetaDeltaFVarIds_4900_; lean_object* v_postponed_4901_; lean_object* v_diag_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4912_; 
v___x_4898_ = lean_st_ref_take(v_a_4894_);
v_mctx_4899_ = lean_ctor_get(v___x_4898_, 0);
v_zetaDeltaFVarIds_4900_ = lean_ctor_get(v___x_4898_, 2);
v_postponed_4901_ = lean_ctor_get(v___x_4898_, 3);
v_diag_4902_ = lean_ctor_get(v___x_4898_, 4);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; 
v_unused_4913_ = lean_ctor_get(v___x_4898_, 1);
lean_dec(v_unused_4913_);
v___x_4904_ = v___x_4898_;
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_diag_4902_);
lean_inc(v_postponed_4901_);
lean_inc(v_zetaDeltaFVarIds_4900_);
lean_inc(v_mctx_4899_);
lean_dec(v___x_4898_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 1, v_cache_4895_);
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_mctx_4899_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_cache_4895_);
lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_zetaDeltaFVarIds_4900_);
lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_postponed_4901_);
lean_ctor_set(v_reuseFailAlloc_4911_, 4, v_diag_4902_);
v___x_4907_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4908_ = lean_st_ref_put(v_a_4894_, v___x_4907_);
v___x_4909_ = lean_box(0);
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
return v___x_4910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4914_, lean_object* v_cache_4915_, lean_object* v_a_x3f_4916_, lean_object* v___y_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4914_, v_cache_4915_, v_a_x3f_4916_);
lean_dec(v_a_x3f_4916_);
lean_dec(v_a_4914_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4919_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4926_; lean_object* v_cache_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4926_ = lean_st_ref_get(v_a_4921_);
v_cache_4927_ = lean_ctor_get(v___x_4926_, 1);
lean_inc_ref(v_cache_4927_);
lean_dec(v___x_4926_);
v___x_4928_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4929_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4919_, v___x_4928_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4946_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4946_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4946_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
lean_inc(v_a_4930_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set_tag(v___x_4932_, 1);
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v___x_4936_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4921_, v_cache_4927_, v___x_4935_);
lean_dec_ref(v___x_4935_);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4943_ == 0)
{
lean_object* v_unused_4944_; 
v_unused_4944_ = lean_ctor_get(v___x_4936_, 0);
lean_dec(v_unused_4944_);
v___x_4938_ = v___x_4936_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_dec(v___x_4936_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v_a_4930_);
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4930_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4947_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4948_ = lean_box(0);
v___x_4949_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4921_, v_cache_4927_, v___x_4948_);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4956_ == 0)
{
lean_object* v_unused_4957_; 
v_unused_4957_ = lean_ctor_get(v___x_4949_, 0);
lean_dec(v_unused_4957_);
v___x_4951_ = v___x_4949_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_dec(v___x_4949_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set_tag(v___x_4951_, 1);
lean_ctor_set(v___x_4951_, 0, v_a_4947_);
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4947_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_object* v___x_4958_; 
lean_dec_ref(v_type_4919_);
v___x_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4925_);
return v___x_4958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4987_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4975_ = v___x_4972_;
v_isShared_4976_ = v_isSharedCheck_4987_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4972_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4987_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
if (lean_obj_tag(v_a_4973_) == 0)
{
uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4980_; 
v___x_4977_ = 0;
v___x_4978_ = lean_box(v___x_4977_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v___x_4978_);
v___x_4980_ = v___x_4975_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
else
{
uint8_t v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4985_; 
lean_dec_ref_known(v_a_4973_, 1);
v___x_4982_ = 1;
v___x_4983_ = lean_box(v___x_4982_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v___x_4983_);
v___x_4985_ = v___x_4975_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4983_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
v_a_4988_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4972_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4972_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_Meta_isTypeFormerType(v_type_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
return v_res_5002_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5003_, lean_object* v_x_5004_){
_start:
{
if (lean_obj_tag(v_x_5003_) == 0)
{
if (lean_obj_tag(v_x_5004_) == 0)
{
uint8_t v___x_5005_; 
v___x_5005_ = 1;
return v___x_5005_;
}
else
{
uint8_t v___x_5006_; 
v___x_5006_ = 0;
return v___x_5006_;
}
}
else
{
if (lean_obj_tag(v_x_5004_) == 0)
{
uint8_t v___x_5007_; 
v___x_5007_ = 0;
return v___x_5007_;
}
else
{
lean_object* v_val_5008_; lean_object* v_val_5009_; uint8_t v___x_5010_; 
v_val_5008_ = lean_ctor_get(v_x_5003_, 0);
v_val_5009_ = lean_ctor_get(v_x_5004_, 0);
v___x_5010_ = lean_level_eq(v_val_5008_, v_val_5009_);
return v___x_5010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5011_, lean_object* v_x_5012_){
_start:
{
uint8_t v_res_5013_; lean_object* v_r_5014_; 
v_res_5013_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5011_, v_x_5012_);
lean_dec(v_x_5012_);
lean_dec(v_x_5011_);
v_r_5014_ = lean_box(v_res_5013_);
return v_r_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5034_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5026_ = v___x_5023_;
v_isShared_5027_ = v_isSharedCheck_5034_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5034_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; uint8_t v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5028_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5029_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5024_, v___x_5028_);
lean_dec(v_a_5024_);
v___x_5030_ = lean_box(v___x_5029_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5030_);
v___x_5032_ = v___x_5026_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5030_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
v_a_5035_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5023_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5023_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Meta_isPropFormerType(v_type_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v___x_5056_; 
lean_inc(v_a_5054_);
lean_inc_ref(v_a_5053_);
lean_inc(v_a_5052_);
lean_inc_ref(v_a_5051_);
v___x_5056_ = lean_infer_type(v_e_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v___x_5058_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v___x_5058_ = l_Lean_Meta_isTypeFormerType(v_a_5057_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_);
return v___x_5058_;
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
v_a_5059_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_5056_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5056_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Meta_isTypeFormer(v_e_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5074_, lean_object* v_maxFVars_x3f_5075_, lean_object* v_k_5076_, uint8_t v_cleanupAnnotations_5077_, uint8_t v_whnfType_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___f_5084_; lean_object* v___x_5085_; 
v___f_5084_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5084_, 0, v_k_5076_);
v___x_5085_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5074_, v_maxFVars_x3f_5075_, v___f_5084_, v_cleanupAnnotations_5077_, v_whnfType_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5085_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
v_a_5094_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5085_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5085_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5102_, lean_object* v_maxFVars_x3f_5103_, lean_object* v_k_5104_, lean_object* v_cleanupAnnotations_5105_, lean_object* v_whnfType_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5112_; uint8_t v_whnfType_boxed_5113_; lean_object* v_res_5114_; 
v_cleanupAnnotations_boxed_5112_ = lean_unbox(v_cleanupAnnotations_5105_);
v_whnfType_boxed_5113_ = lean_unbox(v_whnfType_5106_);
v_res_5114_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5102_, v_maxFVars_x3f_5103_, v_k_5104_, v_cleanupAnnotations_boxed_5112_, v_whnfType_boxed_5113_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5115_, lean_object* v_type_5116_, lean_object* v_maxFVars_x3f_5117_, lean_object* v_k_5118_, uint8_t v_cleanupAnnotations_5119_, uint8_t v_whnfType_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5116_, v_maxFVars_x3f_5117_, v_k_5118_, v_cleanupAnnotations_5119_, v_whnfType_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5127_, lean_object* v_type_5128_, lean_object* v_maxFVars_x3f_5129_, lean_object* v_k_5130_, lean_object* v_cleanupAnnotations_5131_, lean_object* v_whnfType_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5138_; uint8_t v_whnfType_boxed_5139_; lean_object* v_res_5140_; 
v_cleanupAnnotations_boxed_5138_ = lean_unbox(v_cleanupAnnotations_5131_);
v_whnfType_boxed_5139_ = lean_unbox(v_whnfType_5132_);
v_res_5140_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5127_, v_type_5128_, v_maxFVars_x3f_5129_, v_k_5130_, v_cleanupAnnotations_boxed_5138_, v_whnfType_boxed_5139_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
return v_res_5140_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5141_, lean_object* v_as_5142_, size_t v_i_5143_, size_t v_stop_5144_){
_start:
{
uint8_t v___x_5145_; 
v___x_5145_ = lean_usize_dec_eq(v_i_5143_, v_stop_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; uint8_t v___x_5147_; 
v___x_5146_ = lean_array_uget_borrowed(v_as_5142_, v_i_5143_);
v___x_5147_ = lean_expr_eqv(v_a_5141_, v___x_5146_);
if (v___x_5147_ == 0)
{
size_t v___x_5148_; size_t v___x_5149_; 
v___x_5148_ = ((size_t)1ULL);
v___x_5149_ = lean_usize_add(v_i_5143_, v___x_5148_);
v_i_5143_ = v___x_5149_;
goto _start;
}
else
{
return v___x_5147_;
}
}
else
{
uint8_t v___x_5151_; 
v___x_5151_ = 0;
return v___x_5151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5152_, lean_object* v_as_5153_, lean_object* v_i_5154_, lean_object* v_stop_5155_){
_start:
{
size_t v_i_boxed_5156_; size_t v_stop_boxed_5157_; uint8_t v_res_5158_; lean_object* v_r_5159_; 
v_i_boxed_5156_ = lean_unbox_usize(v_i_5154_);
lean_dec(v_i_5154_);
v_stop_boxed_5157_ = lean_unbox_usize(v_stop_5155_);
lean_dec(v_stop_5155_);
v_res_5158_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5152_, v_as_5153_, v_i_boxed_5156_, v_stop_boxed_5157_);
lean_dec_ref(v_as_5153_);
lean_dec_ref(v_a_5152_);
v_r_5159_ = lean_box(v_res_5158_);
return v_r_5159_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5160_, lean_object* v_a_5161_){
_start:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = lean_array_get_size(v_as_5160_);
v___x_5164_ = lean_nat_dec_lt(v___x_5162_, v___x_5163_);
if (v___x_5164_ == 0)
{
return v___x_5164_;
}
else
{
if (v___x_5164_ == 0)
{
return v___x_5164_;
}
else
{
size_t v___x_5165_; size_t v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = ((size_t)0ULL);
v___x_5166_ = lean_usize_of_nat(v___x_5163_);
v___x_5167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5161_, v_as_5160_, v___x_5165_, v___x_5166_);
return v___x_5167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5168_, lean_object* v_a_5169_){
_start:
{
uint8_t v_res_5170_; lean_object* v_r_5171_; 
v_res_5170_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5168_, v_a_5169_);
lean_dec_ref(v_a_5169_);
lean_dec_ref(v_as_5168_);
v_r_5171_ = lean_box(v_res_5170_);
return v_r_5171_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5172_, lean_object* v_e_5173_){
_start:
{
uint8_t v___x_5174_; lean_object* v_d_5176_; lean_object* v_b_5177_; 
v___x_5174_ = l_Lean_Expr_hasFVar(v_e_5173_);
if (v___x_5174_ == 0)
{
lean_dec_ref(v_e_5173_);
return v___x_5174_;
}
else
{
switch(lean_obj_tag(v_e_5173_))
{
case 7:
{
lean_object* v_binderType_5180_; lean_object* v_body_5181_; 
v_binderType_5180_ = lean_ctor_get(v_e_5173_, 1);
lean_inc_ref(v_binderType_5180_);
v_body_5181_ = lean_ctor_get(v_e_5173_, 2);
lean_inc_ref(v_body_5181_);
lean_dec_ref_known(v_e_5173_, 3);
v_d_5176_ = v_binderType_5180_;
v_b_5177_ = v_body_5181_;
goto v___jp_5175_;
}
case 6:
{
lean_object* v_binderType_5182_; lean_object* v_body_5183_; 
v_binderType_5182_ = lean_ctor_get(v_e_5173_, 1);
lean_inc_ref(v_binderType_5182_);
v_body_5183_ = lean_ctor_get(v_e_5173_, 2);
lean_inc_ref(v_body_5183_);
lean_dec_ref_known(v_e_5173_, 3);
v_d_5176_ = v_binderType_5182_;
v_b_5177_ = v_body_5183_;
goto v___jp_5175_;
}
case 10:
{
lean_object* v_expr_5184_; 
v_expr_5184_ = lean_ctor_get(v_e_5173_, 1);
lean_inc_ref(v_expr_5184_);
lean_dec_ref_known(v_e_5173_, 2);
v_e_5173_ = v_expr_5184_;
goto _start;
}
case 8:
{
lean_object* v_type_5186_; lean_object* v_value_5187_; lean_object* v_body_5188_; uint8_t v___x_5189_; 
v_type_5186_ = lean_ctor_get(v_e_5173_, 1);
lean_inc_ref(v_type_5186_);
v_value_5187_ = lean_ctor_get(v_e_5173_, 2);
lean_inc_ref(v_value_5187_);
v_body_5188_ = lean_ctor_get(v_e_5173_, 3);
lean_inc_ref(v_body_5188_);
lean_dec_ref_known(v_e_5173_, 4);
v___x_5189_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5172_, v_type_5186_);
if (v___x_5189_ == 0)
{
uint8_t v___x_5190_; 
v___x_5190_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5172_, v_value_5187_);
if (v___x_5190_ == 0)
{
v_e_5173_ = v_body_5188_;
goto _start;
}
else
{
lean_dec_ref(v_body_5188_);
return v___x_5174_;
}
}
else
{
lean_dec_ref(v_body_5188_);
lean_dec_ref(v_value_5187_);
return v___x_5174_;
}
}
case 5:
{
lean_object* v_fn_5192_; lean_object* v_arg_5193_; uint8_t v___x_5194_; 
v_fn_5192_ = lean_ctor_get(v_e_5173_, 0);
lean_inc_ref(v_fn_5192_);
v_arg_5193_ = lean_ctor_get(v_e_5173_, 1);
lean_inc_ref(v_arg_5193_);
lean_dec_ref_known(v_e_5173_, 2);
v___x_5194_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5172_, v_fn_5192_);
if (v___x_5194_ == 0)
{
v_e_5173_ = v_arg_5193_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5193_);
return v___x_5174_;
}
}
case 11:
{
lean_object* v_struct_5196_; 
v_struct_5196_ = lean_ctor_get(v_e_5173_, 2);
lean_inc_ref(v_struct_5196_);
lean_dec_ref_known(v_e_5173_, 3);
v_e_5173_ = v_struct_5196_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5198_; lean_object* v___x_5199_; uint8_t v___x_5200_; 
v_fvarId_5198_ = lean_ctor_get(v_e_5173_, 0);
lean_inc(v_fvarId_5198_);
lean_dec_ref_known(v_e_5173_, 1);
v___x_5199_ = l_Lean_Expr_fvar___override(v_fvarId_5198_);
v___x_5200_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5172_, v___x_5199_);
lean_dec_ref(v___x_5199_);
return v___x_5200_;
}
default: 
{
uint8_t v___x_5201_; 
lean_dec_ref(v_e_5173_);
v___x_5201_ = 0;
return v___x_5201_;
}
}
}
v___jp_5175_:
{
uint8_t v___x_5178_; 
v___x_5178_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5172_, v_d_5176_);
if (v___x_5178_ == 0)
{
v_e_5173_ = v_b_5177_;
goto _start;
}
else
{
lean_dec_ref(v_b_5177_);
return v___x_5174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5202_, lean_object* v_e_5203_){
_start:
{
uint8_t v_res_5204_; lean_object* v_r_5205_; 
v_res_5204_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5202_, v_e_5203_);
lean_dec_ref(v_xs_5202_);
v_r_5205_ = lean_box(v_res_5204_);
return v_r_5205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5208_ = l_Lean_stringToMessageData(v___x_5207_);
return v___x_5208_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5211_ = l_Lean_stringToMessageData(v___x_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5212_, lean_object* v_type_5213_, lean_object* v_as_5214_, size_t v_sz_5215_, size_t v_i_5216_, lean_object* v_b_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
lean_object* v_a_5224_; uint8_t v___x_5228_; 
v___x_5228_ = lean_usize_dec_lt(v_i_5216_, v_sz_5215_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; 
lean_dec_ref(v_type_5213_);
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v_b_5217_);
return v___x_5229_;
}
else
{
lean_object* v___x_5230_; lean_object* v_a_5231_; uint8_t v___x_5232_; 
v___x_5230_ = lean_box(0);
v_a_5231_ = lean_array_uget_borrowed(v_as_5214_, v_i_5216_);
lean_inc(v_a_5231_);
v___x_5232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5212_, v_a_5231_);
if (v___x_5232_ == 0)
{
v_a_5224_ = v___x_5230_;
goto v___jp_5223_;
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5231_);
v___x_5234_ = l_Lean_MessageData_ofExpr(v_a_5231_);
v___x_5235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5233_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5235_);
lean_ctor_set(v___x_5237_, 1, v___x_5236_);
lean_inc_ref(v_type_5213_);
v___x_5238_ = l_Lean_MessageData_ofExpr(v_type_5213_);
v___x_5239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5237_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5239_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_dec_ref_known(v___x_5240_, 1);
v_a_5224_ = v___x_5230_;
goto v___jp_5223_;
}
else
{
lean_dec_ref(v_type_5213_);
return v___x_5240_;
}
}
}
v___jp_5223_:
{
size_t v___x_5225_; size_t v___x_5226_; 
v___x_5225_ = ((size_t)1ULL);
v___x_5226_ = lean_usize_add(v_i_5216_, v___x_5225_);
v_i_5216_ = v___x_5226_;
v_b_5217_ = v_a_5224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5241_, lean_object* v_type_5242_, lean_object* v_as_5243_, lean_object* v_sz_5244_, lean_object* v_i_5245_, lean_object* v_b_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
size_t v_sz_boxed_5252_; size_t v_i_boxed_5253_; lean_object* v_res_5254_; 
v_sz_boxed_5252_ = lean_unbox_usize(v_sz_5244_);
lean_dec(v_sz_5244_);
v_i_boxed_5253_ = lean_unbox_usize(v_i_5245_);
lean_dec(v_i_5245_);
v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5241_, v_type_5242_, v_as_5243_, v_sz_boxed_5252_, v_i_boxed_5253_, v_b_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec_ref(v_as_5243_);
lean_dec_ref(v_xs_5241_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5255_, size_t v_i_5256_, lean_object* v_bs_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
uint8_t v___x_5263_; 
v___x_5263_ = lean_usize_dec_lt(v_i_5256_, v_sz_5255_);
if (v___x_5263_ == 0)
{
lean_object* v___x_5264_; 
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v_bs_5257_);
return v___x_5264_;
}
else
{
lean_object* v_v_5265_; lean_object* v___x_5266_; 
v_v_5265_ = lean_array_uget_borrowed(v_bs_5257_, v_i_5256_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
lean_inc(v___y_5259_);
lean_inc_ref(v___y_5258_);
lean_inc(v_v_5265_);
v___x_5266_ = lean_infer_type(v_v_5265_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
if (lean_obj_tag(v___x_5266_) == 0)
{
lean_object* v_a_5267_; lean_object* v___x_5268_; lean_object* v_bs_x27_5269_; size_t v___x_5270_; size_t v___x_5271_; lean_object* v___x_5272_; 
v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
lean_inc(v_a_5267_);
lean_dec_ref_known(v___x_5266_, 1);
v___x_5268_ = lean_unsigned_to_nat(0u);
v_bs_x27_5269_ = lean_array_uset(v_bs_5257_, v_i_5256_, v___x_5268_);
v___x_5270_ = ((size_t)1ULL);
v___x_5271_ = lean_usize_add(v_i_5256_, v___x_5270_);
v___x_5272_ = lean_array_uset(v_bs_x27_5269_, v_i_5256_, v_a_5267_);
v_i_5256_ = v___x_5271_;
v_bs_5257_ = v___x_5272_;
goto _start;
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref(v_bs_5257_);
v_a_5274_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5266_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5266_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5282_, lean_object* v_i_5283_, lean_object* v_bs_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
size_t v_sz_boxed_5290_; size_t v_i_boxed_5291_; lean_object* v_res_5292_; 
v_sz_boxed_5290_ = lean_unbox_usize(v_sz_5282_);
lean_dec(v_sz_5282_);
v_i_boxed_5291_ = lean_unbox_usize(v_i_5283_);
lean_dec(v_i_5283_);
v_res_5292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5290_, v_i_boxed_5291_, v_bs_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5292_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5295_ = l_Lean_stringToMessageData(v___x_5294_);
return v___x_5295_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5298_ = l_Lean_stringToMessageData(v___x_5297_);
return v___x_5298_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5301_ = l_Lean_stringToMessageData(v___x_5300_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5302_, lean_object* v_n_5303_, lean_object* v_xs_5304_, lean_object* v_x_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5335_ = lean_array_get_size(v_xs_5304_);
v___x_5336_ = lean_nat_dec_eq(v___x_5335_, v_n_5303_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_dec_ref(v_xs_5304_);
v___x_5337_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5338_ = l_Lean_MessageData_ofExpr(v_type_5302_);
v___x_5339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5337_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
v___x_5340_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5339_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Nat_reprFast(v_n_5303_);
v___x_5343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
v___x_5344_ = l_Lean_MessageData_ofFormat(v___x_5343_);
v___x_5345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5341_);
lean_ctor_set(v___x_5345_, 1, v___x_5344_);
v___x_5346_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5345_);
lean_ctor_set(v___x_5347_, 1, v___x_5346_);
v___x_5348_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5347_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
else
{
lean_dec(v_n_5303_);
goto v___jp_5311_;
}
v___jp_5311_:
{
size_t v_sz_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v_sz_5312_ = lean_array_size(v_xs_5304_);
v___x_5313_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5304_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5312_, v___x_5313_, v_xs_5304_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v_a_5315_; lean_object* v___x_5316_; size_t v_sz_5317_; lean_object* v___x_5318_; 
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
lean_inc(v_a_5315_);
lean_dec_ref_known(v___x_5314_, 1);
v___x_5316_ = lean_box(0);
v_sz_5317_ = lean_array_size(v_a_5315_);
v___x_5318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5304_, v_type_5302_, v_a_5315_, v_sz_5317_, v___x_5313_, v___x_5316_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
lean_dec_ref(v_xs_5304_);
if (lean_obj_tag(v___x_5318_) == 0)
{
lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___x_5318_, 0);
lean_dec(v_unused_5326_);
v___x_5320_ = v___x_5318_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_dec(v___x_5318_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v_a_5315_);
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5315_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
lean_dec(v_a_5315_);
v_a_5327_ = lean_ctor_get(v___x_5318_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5318_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5318_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5304_);
lean_dec_ref(v_type_5302_);
return v___x_5314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5357_, lean_object* v_n_5358_, lean_object* v_xs_5359_, lean_object* v_x_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5357_, v_n_5358_, v_xs_5359_, v_x_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec_ref(v_x_5360_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5367_, lean_object* v_type_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v___f_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; lean_object* v___x_5377_; 
lean_inc(v_n_5367_);
lean_inc_ref(v_type_5368_);
v___f_5374_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5374_, 0, v_type_5368_);
lean_closure_set(v___f_5374_, 1, v_n_5367_);
v___x_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_n_5367_);
v___x_5376_ = 0;
v___x_5377_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5368_, v___x_5375_, v___f_5374_, v___x_5376_, v___x_5376_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5378_, lean_object* v_type_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Lean_Meta_arrowDomainsN(v_n_5378_, v_type_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_);
lean_dec(v_a_5383_);
lean_dec_ref(v_a_5382_);
lean_dec(v_a_5381_);
lean_dec_ref(v_a_5380_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5386_, lean_object* v_e_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_){
_start:
{
lean_object* v___x_5393_; 
lean_inc(v_a_5391_);
lean_inc_ref(v_a_5390_);
lean_inc(v_a_5389_);
lean_inc_ref(v_a_5388_);
v___x_5393_ = lean_infer_type(v_e_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5395_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5394_);
lean_dec_ref_known(v___x_5393_, 1);
v___x_5395_ = l_Lean_Meta_arrowDomainsN(v_n_5386_, v_a_5394_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
return v___x_5395_;
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec(v_n_5386_);
v_a_5396_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5393_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5393_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5404_, lean_object* v_e_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Meta_inferArgumentTypesN(v_n_5404_, v_e_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
return v_res_5411_;
}
}
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_InferType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_InferType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_InferType(builtin);
}
#ifdef __cplusplus
}
#endif
