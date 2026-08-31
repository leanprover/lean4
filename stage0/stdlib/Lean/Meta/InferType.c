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
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ProjReductionKind_ctorIdx(uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_options_688_ = lean_ctor_get(v___y_680_, 1);
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
v_ref_705_ = lean_ctor_get(v___y_702_, 4);
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
lean_object* v_toCold_967_; lean_object* v_options_968_; lean_object* v_currRecDepth_969_; lean_object* v_maxRecDepth_970_; lean_object* v_ref_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v_initHeartbeats_974_; lean_object* v_maxHeartbeats_975_; lean_object* v_currMacroScope_976_; uint8_t v_diag_977_; uint8_t v_suppressElabErrors_978_; lean_object* v_ref_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_toCold_967_ = lean_ctor_get(v___y_964_, 0);
v_options_968_ = lean_ctor_get(v___y_964_, 1);
v_currRecDepth_969_ = lean_ctor_get(v___y_964_, 2);
v_maxRecDepth_970_ = lean_ctor_get(v___y_964_, 3);
v_ref_971_ = lean_ctor_get(v___y_964_, 4);
v_currNamespace_972_ = lean_ctor_get(v___y_964_, 5);
v_openDecls_973_ = lean_ctor_get(v___y_964_, 6);
v_initHeartbeats_974_ = lean_ctor_get(v___y_964_, 7);
v_maxHeartbeats_975_ = lean_ctor_get(v___y_964_, 8);
v_currMacroScope_976_ = lean_ctor_get(v___y_964_, 9);
v_diag_977_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*10);
v_suppressElabErrors_978_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*10 + 1);
v_ref_979_ = l_Lean_replaceRef(v_ref_960_, v_ref_971_);
lean_inc(v_currMacroScope_976_);
lean_inc(v_maxHeartbeats_975_);
lean_inc(v_initHeartbeats_974_);
lean_inc(v_openDecls_973_);
lean_inc(v_currNamespace_972_);
lean_inc(v_maxRecDepth_970_);
lean_inc(v_currRecDepth_969_);
lean_inc_ref(v_options_968_);
lean_inc_ref(v_toCold_967_);
v___x_980_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_980_, 0, v_toCold_967_);
lean_ctor_set(v___x_980_, 1, v_options_968_);
lean_ctor_set(v___x_980_, 2, v_currRecDepth_969_);
lean_ctor_set(v___x_980_, 3, v_maxRecDepth_970_);
lean_ctor_set(v___x_980_, 4, v_ref_979_);
lean_ctor_set(v___x_980_, 5, v_currNamespace_972_);
lean_ctor_set(v___x_980_, 6, v_openDecls_973_);
lean_ctor_set(v___x_980_, 7, v_initHeartbeats_974_);
lean_ctor_set(v___x_980_, 8, v_maxHeartbeats_975_);
lean_ctor_set(v___x_980_, 9, v_currMacroScope_976_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*10, v_diag_977_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*10 + 1, v_suppressElabErrors_978_);
v___x_981_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_961_, v___y_962_, v___y_963_, v___x_980_, v___y_965_);
lean_dec_ref_known(v___x_980_, 10);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_982_, lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_982_, v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v_ref_982_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_ctor_set(v___x_995_, 2, v___x_994_);
lean_ctor_set(v___x_995_, 3, v___x_994_);
lean_ctor_set(v___x_995_, 4, v___x_993_);
lean_ctor_set(v___x_995_, 5, v___x_993_);
lean_ctor_set(v___x_995_, 6, v___x_993_);
lean_ctor_set(v___x_995_, 7, v___x_993_);
lean_ctor_set(v___x_995_, 8, v___x_993_);
lean_ctor_set(v___x_995_, 9, v___x_993_);
lean_ctor_set(v___x_995_, 10, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_unsigned_to_nat(32u);
v___x_997_ = lean_mk_empty_array_with_capacity(v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = ((size_t)5ULL);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_unsigned_to_nat(32u);
v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1004_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1000_);
lean_ctor_set(v___x_1004_, 3, v___x_1000_);
lean_ctor_set_usize(v___x_1004_, 4, v___x_999_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = lean_box(1);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1005_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1030_, lean_object* v_declHint_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_env_1035_; uint8_t v___x_1036_; 
v___x_1034_ = lean_st_ref_get(v___y_1032_);
v_env_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1035_);
lean_dec(v___x_1034_);
v___x_1036_ = l_Lean_Name_isAnonymous(v_declHint_1031_);
if (v___x_1036_ == 0)
{
uint8_t v_isExporting_1037_; 
v_isExporting_1037_ = lean_ctor_get_uint8(v_env_1035_, sizeof(void*)*8);
if (v_isExporting_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1031_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_msg_1030_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
lean_inc_ref(v_env_1035_);
v___x_1039_ = l_Lean_Environment_setExporting(v_env_1035_, v___x_1036_);
lean_inc(v_declHint_1031_);
lean_inc_ref(v___x_1039_);
v___x_1040_ = l_Lean_Environment_contains(v___x_1039_, v_declHint_1031_, v_isExporting_1037_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1031_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_msg_1030_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_c_1047_; lean_object* v___x_1048_; 
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1044_ = l_Lean_Options_empty;
v___x_1045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1039_);
lean_ctor_set(v___x_1045_, 1, v___x_1042_);
lean_ctor_set(v___x_1045_, 2, v___x_1043_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
lean_inc(v_declHint_1031_);
v___x_1046_ = l_Lean_MessageData_ofConstName(v_declHint_1031_, v___x_1036_);
v_c_1047_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1047_, 0, v___x_1045_);
lean_ctor_set(v_c_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1035_, v_declHint_1031_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1031_);
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_c_1047_);
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_note(v___x_1052_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_msg_1030_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
else
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1091_; 
v_val_1056_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1058_ = v___x_1048_;
v_isShared_1059_ = v_isSharedCheck_1091_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1091_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_mod_1063_; uint8_t v___x_1064_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_Lean_Environment_header(v_env_1035_);
lean_dec_ref(v_env_1035_);
v___x_1062_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1061_);
v_mod_1063_ = lean_array_get(v___x_1060_, v___x_1062_, v_val_1056_);
lean_dec(v_val_1056_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = l_Lean_isPrivateName(v_declHint_1031_);
lean_dec(v_declHint_1031_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_c_1047_);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofName(v_mod_1063_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_MessageData_note(v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_msg_1030_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1074_);
v___x_1076_ = v___x_1058_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_c_1047_);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofName(v_mod_1063_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_note(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_msg_1030_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1087_);
v___x_1089_ = v___x_1058_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1092_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1031_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_msg_1030_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1093_, lean_object* v_declHint_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1093_, v_declHint_1094_, v___y_1095_);
lean_dec(v___y_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1098_, lean_object* v_declHint_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v___x_1105_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1098_, v_declHint_1099_, v___y_1103_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1110_ = l_Lean_unknownIdentifierMessageTag;
v___x_1111_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1116_, lean_object* v_declHint_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1116_, v_declHint_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1124_, lean_object* v_msg_1125_, lean_object* v_declHint_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1134_; 
v___x_1132_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1125_, v_declHint_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1124_, v_a_1133_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1135_, lean_object* v_msg_1136_, lean_object* v_declHint_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1135_, v_msg_1136_, v_declHint_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v_ref_1135_);
return v_res_1143_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1150_, lean_object* v_constName_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1157_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1158_ = 0;
lean_inc(v_constName_1151_);
v___x_1159_ = l_Lean_MessageData_ofConstName(v_constName_1151_, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1150_, v___x_1162_, v_constName_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1164_, lean_object* v_constName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1164_, v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v_ref_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_ref_1178_; lean_object* v___x_1179_; 
v_ref_1178_ = lean_ctor_get(v___y_1175_, 4);
v___x_1179_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1178_, v_constName_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v_env_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_st_ref_get(v___y_1191_);
v_env_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_env_1194_);
lean_dec(v___x_1193_);
v___x_1195_ = 0;
lean_inc(v_constName_1187_);
v___x_1196_ = l_Lean_Environment_findConstVal_x3f(v_env_1194_, v_constName_1187_, v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_constName_1187_);
v_val_1198_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 0);
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_val_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1213_, lean_object* v_us_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1220_; 
lean_inc(v_c_1213_);
v___x_1220_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1213_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v_levelParams_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v_levelParams_1222_ = lean_ctor_get(v_a_1221_, 1);
v___x_1223_ = l_List_lengthTR___redArg(v_levelParams_1222_);
v___x_1224_ = l_List_lengthTR___redArg(v_us_1214_);
v___x_1225_ = lean_nat_dec_eq(v___x_1223_, v___x_1224_);
lean_dec(v___x_1224_);
lean_dec(v___x_1223_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_dec(v_a_1221_);
v___x_1226_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1213_, v_us_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_c_1213_);
v___x_1227_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1221_, v_us_1214_, v_a_1218_);
return v___x_1227_;
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_us_1214_);
lean_dec(v_c_1213_);
v_a_1228_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1220_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1220_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1236_, lean_object* v_us_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1236_, v_us_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1244_, lean_object* v_constName_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1252_, v_constName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1260_, lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1261_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_ref_1270_, lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1269_, v_ref_1270_, v_constName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v_ref_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1278_, lean_object* v_ref_1279_, lean_object* v_msg_1280_, lean_object* v_declHint_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1279_, v_msg_1280_, v_declHint_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_ref_1289_, lean_object* v_msg_1290_, lean_object* v_declHint_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1288_, v_ref_1289_, v_msg_1290_, v_declHint_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_ref_1289_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1298_, lean_object* v_declHint_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1298_, v_declHint_1299_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1306_, lean_object* v_declHint_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1306_, v_declHint_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1314_, lean_object* v_ref_1315_, lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1315_, v_msg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_ref_1324_, lean_object* v_msg_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1323_, v_ref_1324_, v_msg_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v_ref_1324_);
return v_res_1331_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1338_, lean_object* v_idx_1339_, lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_00_u03b1_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1349_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1350_ = l_Lean_mkProj(v_structName_1338_, v_idx_1339_, v_e_1340_);
v___x_1351_ = l_Lean_indentExpr(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_indentExpr(v_a_1341_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1356_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1358_, lean_object* v_idx_1359_, lean_object* v_e_1360_, lean_object* v_a_1361_, lean_object* v_00_u03b1_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1358_, v_idx_1359_, v_e_1360_, v_a_1361_, v_00_u03b1_1362_, v_x_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_env_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_st_ref_get(v___y_1374_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = 0;
lean_inc(v_constName_1370_);
v___x_1379_ = l_Lean_Environment_find_x3f(v_env_1377_, v_constName_1370_, v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1380_;
}
else
{
lean_object* v_val_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_constName_1370_);
v_val_1381_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1379_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_val_1381_);
lean_dec(v___x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 0);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_val_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1396_, lean_object* v_structName_1397_, lean_object* v_e_1398_, lean_object* v_idx_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_a_1409_; uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_lt(v_a_1401_, v_upperBound_1396_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_idx_1399_);
lean_dec_ref(v_e_1398_);
lean_dec(v_structName_1397_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_b_1402_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; 
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
v___x_1415_ = lean_whnf(v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
if (lean_obj_tag(v_a_1416_) == 7)
{
lean_object* v_body_1417_; uint8_t v___x_1418_; 
v_body_1417_ = lean_ctor_get(v_a_1416_, 2);
lean_inc_ref(v_body_1417_);
lean_dec_ref_known(v_a_1416_, 3);
v___x_1418_ = l_Lean_Expr_hasLooseBVars(v_body_1417_);
if (v___x_1418_ == 0)
{
v_a_1409_ = v_body_1417_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc_ref(v_e_1398_);
lean_inc(v_a_1401_);
lean_inc(v_structName_1397_);
v___x_1419_ = l_Lean_mkProj(v_structName_1397_, v_a_1401_, v_e_1398_);
v___x_1420_ = lean_expr_instantiate1(v_body_1417_, v___x_1419_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_body_1417_);
v_a_1409_ = v___x_1420_;
goto v___jp_1408_;
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1398_);
lean_inc(v_idx_1399_);
lean_inc(v_structName_1397_);
v___x_1422_ = l_Lean_mkProj(v_structName_1397_, v_idx_1399_, v_e_1398_);
v___x_1423_ = l_Lean_indentExpr(v___x_1422_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1421_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
lean_inc_ref(v_a_1400_);
v___x_1427_ = l_Lean_indentExpr(v_a_1400_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1428_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref_known(v___x_1429_, 1);
v_a_1409_ = v_a_1416_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_a_1416_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_idx_1399_);
lean_dec_ref(v_e_1398_);
lean_dec(v_structName_1397_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_idx_1399_);
lean_dec_ref(v_e_1398_);
lean_dec(v_structName_1397_);
return v___x_1415_;
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_add(v_a_1401_, v___x_1410_);
lean_dec(v_a_1401_);
v_a_1401_ = v___x_1411_;
v_b_1402_ = v_a_1409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1438_, lean_object* v_structName_1439_, lean_object* v_e_1440_, lean_object* v_idx_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1438_, v_structName_1439_, v_e_1440_, v_idx_1441_, v_a_1442_, v_a_1443_, v_b_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v_upperBound_1438_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1451_, lean_object* v_structName_1452_, lean_object* v_e_1453_, lean_object* v_idx_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_a_1464_; uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_lt(v_a_1456_, v_upperBound_1451_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_idx_1454_);
lean_dec_ref(v_e_1453_);
lean_dec(v_structName_1452_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1457_);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; 
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
v___x_1470_ = lean_whnf(v_b_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
if (lean_obj_tag(v_a_1471_) == 7)
{
lean_object* v_body_1472_; uint8_t v___x_1473_; 
v_body_1472_ = lean_ctor_get(v_a_1471_, 2);
lean_inc_ref(v_body_1472_);
lean_dec_ref_known(v_a_1471_, 3);
v___x_1473_ = l_Lean_Expr_hasLooseBVars(v_body_1472_);
if (v___x_1473_ == 0)
{
v_a_1464_ = v_body_1472_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc_ref(v_e_1453_);
lean_inc(v_a_1456_);
lean_inc(v_structName_1452_);
v___x_1474_ = l_Lean_mkProj(v_structName_1452_, v_a_1456_, v_e_1453_);
v___x_1475_ = lean_expr_instantiate1(v_body_1472_, v___x_1474_);
lean_dec_ref(v___x_1474_);
lean_dec_ref(v_body_1472_);
v_a_1464_ = v___x_1475_;
goto v___jp_1463_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1476_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1453_);
lean_inc(v_idx_1454_);
lean_inc(v_structName_1452_);
v___x_1477_ = l_Lean_mkProj(v_structName_1452_, v_idx_1454_, v_e_1453_);
v___x_1478_ = l_Lean_indentExpr(v___x_1477_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1476_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc_ref(v_a_1455_);
v___x_1482_ = l_Lean_indentExpr(v_a_1455_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1483_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref_known(v___x_1484_, 1);
v_a_1464_ = v_a_1471_;
goto v___jp_1463_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1471_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_idx_1454_);
lean_dec_ref(v_e_1453_);
lean_dec(v_structName_1452_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_idx_1454_);
lean_dec_ref(v_e_1453_);
lean_dec(v_structName_1452_);
return v___x_1470_;
}
}
v___jp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_a_1456_, v___x_1465_);
lean_dec(v_a_1456_);
v___x_1467_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1451_, v_structName_1452_, v_e_1453_, v_idx_1454_, v_a_1455_, v___x_1466_, v_a_1464_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1493_, lean_object* v_structName_1494_, lean_object* v_e_1495_, lean_object* v_idx_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1493_, v_structName_1494_, v_e_1495_, v_idx_1496_, v_a_1497_, v_a_1498_, v_b_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v_upperBound_1493_);
return v_res_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1506_; lean_object* v_dummy_1507_; 
v___x_1506_ = lean_box(0);
v_dummy_1507_ = l_Lean_Expr_sort___override(v___x_1506_);
return v_dummy_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1508_, lean_object* v_idx_1509_, lean_object* v_e_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
lean_inc(v_a_1514_);
lean_inc_ref(v_a_1513_);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
lean_inc_ref(v_e_1510_);
v___x_1516_ = lean_infer_type(v_e_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
lean_inc(v_a_1514_);
lean_inc_ref(v_a_1513_);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
v___x_1518_ = lean_whnf(v_a_1517_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Expr_getAppFn(v_a_1519_);
if (lean_obj_tag(v___x_1520_) == 4)
{
lean_object* v_declName_1521_; lean_object* v_us_1522_; lean_object* v___x_1523_; lean_object* v_env_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v_declName_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_declName_1521_);
v_us_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_us_1522_);
lean_dec_ref_known(v___x_1520_, 2);
v___x_1523_ = lean_st_ref_get(v_a_1514_);
v_env_1527_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_env_1527_);
lean_dec(v___x_1523_);
v___x_1528_ = 0;
v___x_1529_ = l_Lean_Environment_find_x3f(v_env_1527_, v_declName_1521_, v___x_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_us_1522_);
v___x_1530_ = lean_box(0);
v___x_1531_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1530_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1531_;
}
else
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1529_, 1);
if (lean_obj_tag(v_val_1532_) == 5)
{
lean_object* v_val_1533_; lean_object* v_ctors_1534_; 
v_val_1533_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_val_1533_);
lean_dec_ref_known(v_val_1532_, 1);
v_ctors_1534_ = lean_ctor_get(v_val_1533_, 4);
lean_inc(v_ctors_1534_);
if (lean_obj_tag(v_ctors_1534_) == 1)
{
lean_object* v_tail_1535_; 
v_tail_1535_ = lean_ctor_get(v_ctors_1534_, 1);
if (lean_obj_tag(v_tail_1535_) == 0)
{
lean_object* v_toConstantVal_1536_; lean_object* v_numParams_1537_; lean_object* v_numIndices_1538_; lean_object* v_head_1539_; lean_object* v___x_1540_; 
v_toConstantVal_1536_ = lean_ctor_get(v_val_1533_, 0);
lean_inc_ref(v_toConstantVal_1536_);
v_numParams_1537_ = lean_ctor_get(v_val_1533_, 1);
lean_inc(v_numParams_1537_);
v_numIndices_1538_ = lean_ctor_get(v_val_1533_, 2);
lean_inc(v_numIndices_1538_);
lean_dec_ref(v_val_1533_);
v_head_1539_ = lean_ctor_get(v_ctors_1534_, 0);
lean_inc(v_head_1539_);
lean_dec_ref_known(v_ctors_1534_, 2);
v___x_1540_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1539_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
if (lean_obj_tag(v_a_1541_) == 6)
{
lean_object* v_val_1542_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_name_1582_; uint8_t v___x_1583_; 
v_val_1542_ = lean_ctor_get(v_a_1541_, 0);
lean_inc_ref(v_val_1542_);
lean_dec_ref_known(v_a_1541_, 1);
v_name_1582_ = lean_ctor_get(v_toConstantVal_1536_, 0);
lean_inc(v_name_1582_);
lean_dec_ref(v_toConstantVal_1536_);
v___x_1583_ = lean_name_eq(v_name_1582_, v_structName_1508_);
lean_dec(v_name_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_val_1542_);
lean_dec(v_numIndices_1538_);
lean_dec(v_numParams_1537_);
lean_dec(v_us_1522_);
v___x_1584_ = lean_box(0);
v___x_1585_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1584_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
v___y_1544_ = v_a_1511_;
v___y_1545_ = v_a_1512_;
v___y_1546_ = v_a_1513_;
v___y_1547_ = v_a_1514_;
goto v___jp_1543_;
}
v___jp_1543_:
{
lean_object* v_dummy_1548_; lean_object* v_nargs_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_dummy_1548_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1549_ = l_Lean_Expr_getAppNumArgs(v_a_1519_);
lean_inc(v_nargs_1549_);
v___x_1550_ = lean_mk_array(v_nargs_1549_, v_dummy_1548_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_sub(v_nargs_1549_, v___x_1551_);
lean_dec(v_nargs_1549_);
lean_inc(v_a_1519_);
v___x_1553_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1519_, v___x_1550_, v___x_1552_);
v___x_1554_ = lean_nat_add(v_numParams_1537_, v_numIndices_1538_);
lean_dec(v_numIndices_1538_);
v___x_1555_ = lean_array_get_size(v___x_1553_);
v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
lean_dec(v___x_1554_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v___x_1553_);
lean_dec_ref(v_val_1542_);
lean_dec(v_numParams_1537_);
lean_dec(v_us_1522_);
v___x_1557_ = lean_box(0);
v___x_1558_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1557_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1558_;
}
else
{
lean_object* v_toConstantVal_1559_; lean_object* v_name_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_toConstantVal_1559_ = lean_ctor_get(v_val_1542_, 0);
lean_inc_ref(v_toConstantVal_1559_);
lean_dec_ref(v_val_1542_);
v_name_1560_ = lean_ctor_get(v_toConstantVal_1559_, 0);
lean_inc(v_name_1560_);
lean_dec_ref(v_toConstantVal_1559_);
v___x_1561_ = l_Lean_mkConst(v_name_1560_, v_us_1522_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = l_Array_toSubarray___redArg(v___x_1553_, v___x_1562_, v_numParams_1537_);
v___x_1564_ = l_Subarray_copy___redArg(v___x_1563_);
v___x_1565_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1561_, v___x_1564_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v_a_1519_);
lean_inc_ref(v_e_1510_);
lean_inc(v_structName_1508_);
lean_inc(v_idx_1509_);
v___x_1567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1509_, v_structName_1508_, v_e_1510_, v_idx_1509_, v_a_1519_, v___x_1562_, v_a_1566_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
lean_inc(v___y_1547_);
lean_inc_ref(v___y_1546_);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
v___x_1569_ = lean_whnf(v_a_1568_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1581_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
if (lean_obj_tag(v_a_1570_) == 7)
{
lean_object* v_binderType_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
v_binderType_1574_ = lean_ctor_get(v_a_1570_, 1);
lean_inc_ref(v_binderType_1574_);
lean_dec_ref_known(v_a_1570_, 3);
v___x_1575_ = lean_expr_consume_type_annotations(v_binderType_1574_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1572_);
lean_dec(v_a_1570_);
v___x_1579_ = lean_box(0);
v___x_1580_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1579_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1580_;
}
}
}
else
{
lean_dec(v_a_1519_);
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
return v___x_1569_;
}
}
else
{
lean_dec(v_a_1519_);
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
return v___x_1567_;
}
}
else
{
lean_dec(v_a_1519_);
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
return v___x_1565_;
}
}
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v_a_1541_);
lean_dec(v_numIndices_1538_);
lean_dec(v_numParams_1537_);
lean_dec_ref(v_toConstantVal_1536_);
lean_dec(v_us_1522_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1594_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1595_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_numIndices_1538_);
lean_dec(v_numParams_1537_);
lean_dec_ref(v_toConstantVal_1536_);
lean_dec(v_us_1522_);
lean_dec(v_a_1519_);
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
v_a_1596_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1540_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1540_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1534_, 2);
lean_dec_ref(v_val_1533_);
lean_dec(v_us_1522_);
goto v___jp_1524_;
}
}
else
{
lean_dec(v_ctors_1534_);
lean_dec_ref(v_val_1533_);
lean_dec(v_us_1522_);
goto v___jp_1524_;
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_val_1532_);
lean_dec(v_us_1522_);
v___x_1604_ = lean_box(0);
v___x_1605_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1604_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1605_;
}
}
v___jp_1524_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1525_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v___x_1520_);
v___x_1606_ = lean_box(0);
v___x_1607_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1508_, v_idx_1509_, v_e_1510_, v_a_1519_, lean_box(0), v___x_1606_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1607_;
}
}
else
{
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
return v___x_1518_;
}
}
else
{
lean_dec_ref(v_e_1510_);
lean_dec(v_idx_1509_);
lean_dec(v_structName_1508_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1608_, lean_object* v_idx_1609_, lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1608_, v_idx_1609_, v_e_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1617_, lean_object* v_structName_1618_, lean_object* v_e_1619_, lean_object* v_idx_1620_, lean_object* v_a_1621_, lean_object* v_inst_1622_, lean_object* v_R_1623_, lean_object* v_a_1624_, lean_object* v_b_1625_, lean_object* v_c_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1617_, v_structName_1618_, v_e_1619_, v_idx_1620_, v_a_1621_, v_a_1624_, v_b_1625_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1633_, lean_object* v_structName_1634_, lean_object* v_e_1635_, lean_object* v_idx_1636_, lean_object* v_a_1637_, lean_object* v_inst_1638_, lean_object* v_R_1639_, lean_object* v_a_1640_, lean_object* v_b_1641_, lean_object* v_c_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1633_, v_structName_1634_, v_e_1635_, v_idx_1636_, v_a_1637_, v_inst_1638_, v_R_1639_, v_a_1640_, v_b_1641_, v_c_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v_upperBound_1633_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1649_, lean_object* v_structName_1650_, lean_object* v_e_1651_, lean_object* v_idx_1652_, lean_object* v_a_1653_, lean_object* v_inst_1654_, lean_object* v_R_1655_, lean_object* v_a_1656_, lean_object* v_b_1657_, lean_object* v_c_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1649_, v_structName_1650_, v_e_1651_, v_idx_1652_, v_a_1653_, v_a_1656_, v_b_1657_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1665_, lean_object* v_structName_1666_, lean_object* v_e_1667_, lean_object* v_idx_1668_, lean_object* v_a_1669_, lean_object* v_inst_1670_, lean_object* v_R_1671_, lean_object* v_a_1672_, lean_object* v_b_1673_, lean_object* v_c_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1665_, v_structName_1666_, v_e_1667_, v_idx_1668_, v_a_1669_, v_inst_1670_, v_R_1671_, v_a_1672_, v_b_1673_, v_c_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_upperBound_1665_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1691_ = l_Lean_indentExpr(v_type_1684_);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1692_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1701_, lean_object* v_type_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_type_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1709_, v_type_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_ks_1721_; lean_object* v_vs_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1746_; 
v_ks_1721_ = lean_ctor_get(v_x_1717_, 0);
v_vs_1722_ = lean_ctor_get(v_x_1717_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1717_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1724_ = v_x_1717_;
v_isShared_1725_ = v_isSharedCheck_1746_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_vs_1722_);
lean_inc(v_ks_1721_);
lean_dec(v_x_1717_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1746_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_ks_1721_);
v___x_1727_ = lean_nat_dec_lt(v_x_1718_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec(v_x_1718_);
v___x_1728_ = lean_array_push(v_ks_1721_, v_x_1719_);
v___x_1729_ = lean_array_push(v_vs_1722_, v_x_1720_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1729_);
lean_ctor_set(v___x_1724_, 0, v___x_1728_);
v___x_1731_ = v___x_1724_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
else
{
lean_object* v_k_x27_1733_; uint8_t v___x_1734_; 
v_k_x27_1733_ = lean_array_fget_borrowed(v_ks_1721_, v_x_1718_);
v___x_1734_ = l_Lean_instBEqMVarId_beq(v_x_1719_, v_k_x27_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1736_; 
if (v_isShared_1725_ == 0)
{
v___x_1736_ = v___x_1724_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_ks_1721_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_vs_1722_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_x_1718_, v___x_1737_);
lean_dec(v_x_1718_);
v_x_1717_ = v___x_1736_;
v_x_1718_ = v___x_1738_;
goto _start;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = lean_array_fset(v_ks_1721_, v_x_1718_, v_x_1719_);
v___x_1742_ = lean_array_fset(v_vs_1722_, v_x_1718_, v_x_1720_);
lean_dec(v_x_1718_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1742_);
lean_ctor_set(v___x_1724_, 0, v___x_1741_);
v___x_1744_ = v___x_1724_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1747_, lean_object* v_k_1748_, lean_object* v_v_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1747_, v___x_1750_, v_k_1748_, v_v_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1753_, size_t v_x_1754_, size_t v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
if (lean_obj_tag(v_x_1753_) == 0)
{
lean_object* v_es_1758_; size_t v___x_1759_; size_t v___x_1760_; lean_object* v_j_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_es_1758_ = lean_ctor_get(v_x_1753_, 0);
v___x_1759_ = ((size_t)31ULL);
v___x_1760_ = lean_usize_land(v_x_1754_, v___x_1759_);
v_j_1761_ = lean_usize_to_nat(v___x_1760_);
v___x_1762_ = lean_array_get_size(v_es_1758_);
v___x_1763_ = lean_nat_dec_lt(v_j_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec(v_j_1761_);
lean_dec(v_x_1757_);
lean_dec(v_x_1756_);
return v_x_1753_;
}
else
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1802_; 
lean_inc_ref(v_es_1758_);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_x_1753_, 0);
lean_dec(v_unused_1803_);
v___x_1765_ = v_x_1753_;
v_isShared_1766_ = v_isSharedCheck_1802_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v_x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1802_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_v_1767_; lean_object* v___x_1768_; lean_object* v_xs_x27_1769_; lean_object* v___y_1771_; 
v_v_1767_ = lean_array_fget(v_es_1758_, v_j_1761_);
v___x_1768_ = lean_box(0);
v_xs_x27_1769_ = lean_array_fset(v_es_1758_, v_j_1761_, v___x_1768_);
switch(lean_obj_tag(v_v_1767_))
{
case 0:
{
lean_object* v_key_1776_; lean_object* v_val_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_key_1776_ = lean_ctor_get(v_v_1767_, 0);
v_val_1777_ = lean_ctor_get(v_v_1767_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_v_1767_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1779_ = v_v_1767_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_val_1777_);
lean_inc(v_key_1776_);
lean_dec(v_v_1767_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Lean_instBEqMVarId_beq(v_x_1756_, v_key_1776_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_del_object(v___x_1779_);
v___x_1782_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1776_, v_val_1777_, v_x_1756_, v_x_1757_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___y_1771_ = v___x_1783_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1785_; 
lean_dec(v_val_1777_);
lean_dec(v_key_1776_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v_x_1757_);
lean_ctor_set(v___x_1779_, 0, v_x_1756_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_x_1756_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_x_1757_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v___y_1771_ = v___x_1785_;
goto v___jp_1770_;
}
}
}
}
case 1:
{
lean_object* v_node_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1800_; 
v_node_1788_ = lean_ctor_get(v_v_1767_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_v_1767_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1790_ = v_v_1767_;
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_node_1788_);
lean_dec(v_v_1767_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1800_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
size_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1792_ = ((size_t)5ULL);
v___x_1793_ = lean_usize_shift_right(v_x_1754_, v___x_1792_);
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_add(v_x_1755_, v___x_1794_);
v___x_1796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1788_, v___x_1793_, v___x_1795_, v_x_1756_, v_x_1757_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1796_);
v___x_1798_ = v___x_1790_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v___y_1771_ = v___x_1798_;
goto v___jp_1770_;
}
}
}
default: 
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_x_1756_);
lean_ctor_set(v___x_1801_, 1, v_x_1757_);
v___y_1771_ = v___x_1801_;
goto v___jp_1770_;
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_array_fset(v_xs_x27_1769_, v_j_1761_, v___y_1771_);
lean_dec(v_j_1761_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1772_);
v___x_1774_ = v___x_1765_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_ks_1804_; lean_object* v_vs_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1823_; 
v_ks_1804_ = lean_ctor_get(v_x_1753_, 0);
v_vs_1805_ = lean_ctor_get(v_x_1753_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1753_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1807_ = v_x_1753_;
v_isShared_1808_ = v_isSharedCheck_1823_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_vs_1805_);
lean_inc(v_ks_1804_);
lean_dec(v_x_1753_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1823_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_ks_1804_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_vs_1805_);
v___x_1810_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v_newNode_1811_; size_t v___x_1812_; uint8_t v___x_1813_; 
v_newNode_1811_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1810_, v_x_1756_, v_x_1757_);
v___x_1812_ = ((size_t)7ULL);
v___x_1813_ = lean_usize_dec_le(v___x_1812_, v_x_1755_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1814_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1811_);
v___x_1815_ = lean_unsigned_to_nat(4u);
v___x_1816_ = lean_nat_dec_lt(v___x_1814_, v___x_1815_);
lean_dec(v___x_1814_);
if (v___x_1816_ == 0)
{
lean_object* v_ks_1817_; lean_object* v_vs_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_ks_1817_ = lean_ctor_get(v_newNode_1811_, 0);
lean_inc_ref(v_ks_1817_);
v_vs_1818_ = lean_ctor_get(v_newNode_1811_, 1);
lean_inc_ref(v_vs_1818_);
lean_dec_ref(v_newNode_1811_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1755_, v_ks_1817_, v_vs_1818_, v___x_1819_, v___x_1820_);
lean_dec_ref(v_vs_1818_);
lean_dec_ref(v_ks_1817_);
return v___x_1821_;
}
else
{
return v_newNode_1811_;
}
}
else
{
return v_newNode_1811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1824_, lean_object* v_keys_1825_, lean_object* v_vals_1826_, lean_object* v_i_1827_, lean_object* v_entries_1828_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_array_get_size(v_keys_1825_);
v___x_1830_ = lean_nat_dec_lt(v_i_1827_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_dec(v_i_1827_);
return v_entries_1828_;
}
else
{
lean_object* v_k_1831_; lean_object* v_v_1832_; uint64_t v___x_1833_; size_t v_h_1834_; size_t v___x_1835_; lean_object* v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; size_t v___x_1839_; size_t v_h_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_k_1831_ = lean_array_fget_borrowed(v_keys_1825_, v_i_1827_);
v_v_1832_ = lean_array_fget_borrowed(v_vals_1826_, v_i_1827_);
v___x_1833_ = l_Lean_instHashableMVarId_hash(v_k_1831_);
v_h_1834_ = lean_uint64_to_usize(v___x_1833_);
v___x_1835_ = ((size_t)5ULL);
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_sub(v_depth_1824_, v___x_1837_);
v___x_1839_ = lean_usize_mul(v___x_1835_, v___x_1838_);
v_h_1840_ = lean_usize_shift_right(v_h_1834_, v___x_1839_);
v___x_1841_ = lean_nat_add(v_i_1827_, v___x_1836_);
lean_dec(v_i_1827_);
lean_inc(v_v_1832_);
lean_inc(v_k_1831_);
v___x_1842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1828_, v_h_1840_, v_depth_1824_, v_k_1831_, v_v_1832_);
v_i_1827_ = v___x_1841_;
v_entries_1828_ = v___x_1842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1844_, lean_object* v_keys_1845_, lean_object* v_vals_1846_, lean_object* v_i_1847_, lean_object* v_entries_1848_){
_start:
{
size_t v_depth_boxed_1849_; lean_object* v_res_1850_; 
v_depth_boxed_1849_ = lean_unbox_usize(v_depth_1844_);
lean_dec(v_depth_1844_);
v_res_1850_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1849_, v_keys_1845_, v_vals_1846_, v_i_1847_, v_entries_1848_);
lean_dec_ref(v_vals_1846_);
lean_dec_ref(v_keys_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
size_t v_x_1146__boxed_1856_; size_t v_x_1147__boxed_1857_; lean_object* v_res_1858_; 
v_x_1146__boxed_1856_ = lean_unbox_usize(v_x_1852_);
lean_dec(v_x_1852_);
v_x_1147__boxed_1857_ = lean_unbox_usize(v_x_1853_);
lean_dec(v_x_1853_);
v_res_1858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1851_, v_x_1146__boxed_1856_, v_x_1147__boxed_1857_, v_x_1854_, v_x_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
uint64_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = l_Lean_instHashableMVarId_hash(v_x_1860_);
v___x_1863_ = lean_uint64_to_usize(v___x_1862_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1859_, v___x_1863_, v___x_1864_, v_x_1860_, v_x_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1866_, lean_object* v_val_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v_mctx_1871_; lean_object* v_cache_1872_; lean_object* v_zetaDeltaFVarIds_1873_; lean_object* v_postponed_1874_; lean_object* v_diag_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1904_; 
v___x_1870_ = lean_st_ref_take(v___y_1868_);
v_mctx_1871_ = lean_ctor_get(v___x_1870_, 0);
v_cache_1872_ = lean_ctor_get(v___x_1870_, 1);
v_zetaDeltaFVarIds_1873_ = lean_ctor_get(v___x_1870_, 2);
v_postponed_1874_ = lean_ctor_get(v___x_1870_, 3);
v_diag_1875_ = lean_ctor_get(v___x_1870_, 4);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1877_ = v___x_1870_;
v_isShared_1878_ = v_isSharedCheck_1904_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_diag_1875_);
lean_inc(v_postponed_1874_);
lean_inc(v_zetaDeltaFVarIds_1873_);
lean_inc(v_cache_1872_);
lean_inc(v_mctx_1871_);
lean_dec(v___x_1870_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1904_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_depth_1879_; lean_object* v_levelAssignDepth_1880_; lean_object* v_lmvarCounter_1881_; lean_object* v_mvarCounter_1882_; lean_object* v_lDecls_1883_; lean_object* v_decls_1884_; lean_object* v_userNames_1885_; lean_object* v_lAssignment_1886_; lean_object* v_eAssignment_1887_; lean_object* v_dAssignment_1888_; lean_object* v_instanceTypedMVars_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1903_; 
v_depth_1879_ = lean_ctor_get(v_mctx_1871_, 0);
v_levelAssignDepth_1880_ = lean_ctor_get(v_mctx_1871_, 1);
v_lmvarCounter_1881_ = lean_ctor_get(v_mctx_1871_, 2);
v_mvarCounter_1882_ = lean_ctor_get(v_mctx_1871_, 3);
v_lDecls_1883_ = lean_ctor_get(v_mctx_1871_, 4);
v_decls_1884_ = lean_ctor_get(v_mctx_1871_, 5);
v_userNames_1885_ = lean_ctor_get(v_mctx_1871_, 6);
v_lAssignment_1886_ = lean_ctor_get(v_mctx_1871_, 7);
v_eAssignment_1887_ = lean_ctor_get(v_mctx_1871_, 8);
v_dAssignment_1888_ = lean_ctor_get(v_mctx_1871_, 9);
v_instanceTypedMVars_1889_ = lean_ctor_get(v_mctx_1871_, 10);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_mctx_1871_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1891_ = v_mctx_1871_;
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_instanceTypedMVars_1889_);
lean_inc(v_dAssignment_1888_);
lean_inc(v_eAssignment_1887_);
lean_inc(v_lAssignment_1886_);
lean_inc(v_userNames_1885_);
lean_inc(v_decls_1884_);
lean_inc(v_lDecls_1883_);
lean_inc(v_mvarCounter_1882_);
lean_inc(v_lmvarCounter_1881_);
lean_inc(v_levelAssignDepth_1880_);
lean_inc(v_depth_1879_);
lean_dec(v_mctx_1871_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1887_, v_mvarId_1866_, v_val_1867_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 8, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_depth_1879_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_levelAssignDepth_1880_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_lmvarCounter_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_mvarCounter_1882_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_lDecls_1883_);
lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_decls_1884_);
lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_userNames_1885_);
lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_lAssignment_1886_);
lean_ctor_set(v_reuseFailAlloc_1902_, 8, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_dAssignment_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 10, v_instanceTypedMVars_1889_);
v___x_1895_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1895_);
v___x_1897_ = v___x_1877_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_cache_1872_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_zetaDeltaFVarIds_1873_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_postponed_1874_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_diag_1875_);
v___x_1897_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_st_ref_put(v___y_1868_, v___x_1897_);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1905_, lean_object* v_val_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1905_, v_val_1906_, v___y_1907_);
lean_dec(v___y_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc_ref(v_type_1910_);
v___x_1916_ = lean_infer_type(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l_Lean_Meta_whnfD(v_a_1917_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1953_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
switch(lean_obj_tag(v_a_1919_))
{
case 3:
{
lean_object* v_u_1923_; lean_object* v___x_1925_; 
lean_dec_ref(v_type_1910_);
v_u_1923_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_u_1923_);
lean_dec_ref_known(v_a_1919_, 1);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_u_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_u_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
case 2:
{
lean_object* v_mvarId_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1921_);
v_mvarId_1927_ = lean_ctor_get(v_a_1919_, 0);
lean_inc_n(v_mvarId_1927_, 2);
lean_dec_ref_known(v_a_1919_, 1);
v___x_1928_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1927_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v_type_1910_);
v___x_1931_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_n(v_a_1932_, 2);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_mkSort(v_a_1932_);
v___x_1934_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1927_, v___x_1933_, v_a_1912_);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1934_, 0);
lean_dec(v_unused_1942_);
v___x_1936_ = v___x_1934_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v___x_1934_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_1932_);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1932_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_dec(v_mvarId_1927_);
return v___x_1931_;
}
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_mvarId_1927_);
v___x_1943_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1943_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_mvarId_1927_);
lean_dec_ref(v_type_1910_);
v_a_1944_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1928_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1928_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
default: 
{
lean_object* v___x_1952_; 
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
v___x_1952_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_type_1910_);
v_a_1954_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1918_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1918_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_type_1910_);
v_a_1962_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1916_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1916_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Meta_getLevel(v_type_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1977_, lean_object* v_val_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1977_, v_val_1978_, v___y_1980_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1985_, lean_object* v_val_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1985_, v_val_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, size_t v_x_2000_, size_t v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1999_, v_x_2000_, v_x_2001_, v_x_2002_, v_x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
size_t v_x_1495__boxed_2011_; size_t v_x_1496__boxed_2012_; lean_object* v_res_2013_; 
v_x_1495__boxed_2011_ = lean_unbox_usize(v_x_2007_);
lean_dec(v_x_2007_);
v_x_1496__boxed_2012_ = lean_unbox_usize(v_x_2008_);
lean_dec(v_x_2008_);
v_res_2013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2005_, v_x_2006_, v_x_1495__boxed_2011_, v_x_1496__boxed_2012_, v_x_2009_, v_x_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2014_, lean_object* v_n_2015_, lean_object* v_k_2016_, lean_object* v_v_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2015_, v_k_2016_, v_v_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2019_, size_t v_depth_2020_, lean_object* v_keys_2021_, lean_object* v_vals_2022_, lean_object* v_heq_2023_, lean_object* v_i_2024_, lean_object* v_entries_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2020_, v_keys_2021_, v_vals_2022_, v_i_2024_, v_entries_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2027_, lean_object* v_depth_2028_, lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_heq_2031_, lean_object* v_i_2032_, lean_object* v_entries_2033_){
_start:
{
size_t v_depth_boxed_2034_; lean_object* v_res_2035_; 
v_depth_boxed_2034_ = lean_unbox_usize(v_depth_2028_);
lean_dec(v_depth_2028_);
v_res_2035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2027_, v_depth_boxed_2034_, v_keys_2029_, v_vals_2030_, v_heq_2031_, v_i_2032_, v_entries_2033_);
lean_dec_ref(v_vals_2030_);
lean_dec_ref(v_keys_2029_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2037_, v_x_2038_, v_x_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2042_, lean_object* v_b_2043_, lean_object* v_c_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
v___x_2050_ = lean_apply_7(v_k_2042_, v_b_2043_, v_c_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, lean_box(0));
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2051_, lean_object* v_b_2052_, lean_object* v_c_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2051_, v_b_2052_, v_c_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2060_, lean_object* v_k_2061_, uint8_t v_cleanupAnnotations_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___f_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2068_, 0, v_k_2061_);
v___x_2069_ = 0;
v___x_2070_ = lean_box(0);
v___x_2071_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2069_, v___x_2070_, v_type_2060_, v___f_2068_, v_cleanupAnnotations_2062_, v___x_2069_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2088_, lean_object* v_k_2089_, lean_object* v_cleanupAnnotations_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2096_; lean_object* v_res_2097_; 
v_cleanupAnnotations_boxed_2096_ = lean_unbox(v_cleanupAnnotations_2090_);
v_res_2097_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2088_, v_k_2089_, v_cleanupAnnotations_boxed_2096_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2098_, lean_object* v_type_2099_, lean_object* v_k_2100_, uint8_t v_cleanupAnnotations_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2099_, v_k_2100_, v_cleanupAnnotations_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_type_2109_, lean_object* v_k_2110_, lean_object* v_cleanupAnnotations_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2117_; lean_object* v_res_2118_; 
v_cleanupAnnotations_boxed_2117_ = lean_unbox(v_cleanupAnnotations_2111_);
v_res_2118_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2108_, v_type_2109_, v_k_2110_, v_cleanupAnnotations_boxed_2117_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2119_, size_t v_i_2120_, size_t v_stop_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_usize_dec_eq(v_i_2120_, v_stop_2121_);
if (v___x_2128_ == 0)
{
size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_sub(v_i_2120_, v___x_2129_);
v___x_2131_ = lean_array_uget_borrowed(v_as_2119_, v___x_2130_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
lean_inc(v___x_2131_);
v___x_2132_ = lean_infer_type(v___x_2131_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Meta_getLevel(v_a_2133_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_mkLevelIMax_x27(v_a_2135_, v_b_2122_);
v_i_2120_ = v___x_2130_;
v_b_2122_ = v___x_2136_;
goto _start;
}
else
{
lean_dec(v_b_2122_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2134_, 1);
v_i_2120_ = v___x_2130_;
v_b_2122_ = v_a_2138_;
goto _start;
}
else
{
return v___x_2134_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_b_2122_);
v_a_2140_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2132_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2132_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_b_2122_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v_i_boxed_2158_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2149_, v_i_boxed_2158_, v_stop_boxed_2159_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2161_, lean_object* v_e_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___y_2169_; lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Meta_getLevel(v_e_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
v___x_2190_ = lean_array_get_size(v_xs_2161_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_lt(v___x_2191_, v___x_2190_);
if (v___x_2192_ == 0)
{
lean_dec(v_a_2189_);
v___y_2169_ = v___x_2188_;
goto v___jp_2168_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
lean_dec_ref_known(v___x_2188_, 1);
v___x_2193_ = lean_usize_of_nat(v___x_2190_);
v___x_2194_ = ((size_t)0ULL);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2161_, v___x_2193_, v___x_2194_, v_a_2189_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
v___y_2169_ = v___x_2195_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_a_2196_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2188_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2188_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
v___jp_2168_:
{
if (lean_obj_tag(v___y_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2179_; 
v_a_2170_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2172_ = v___y_2169_;
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___y_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2174_ = l_Lean_Level_normalize(v_a_2170_);
lean_dec(v_a_2170_);
v___x_2175_ = l_Lean_mkSort(v___x_2174_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2175_);
v___x_2177_ = v___x_2172_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___y_2169_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___y_2169_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2204_, lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2204_, v_e_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec_ref(v_xs_2204_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___f_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
v___f_2219_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2220_ = 0;
v___x_2221_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2213_, v___f_2219_, v___x_2220_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2229_, lean_object* v_k_2230_, uint8_t v_cleanupAnnotations_2231_, uint8_t v_preserveNondepLet_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___f_2238_; uint8_t v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2238_, 0, v_k_2230_);
v___x_2239_ = 1;
v___x_2240_ = 0;
v___x_2241_ = lean_box(0);
v___x_2242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2229_, v___x_2239_, v___x_2239_, v_preserveNondepLet_2232_, v___x_2240_, v___x_2241_, v___f_2238_, v_cleanupAnnotations_2231_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2242_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2259_, lean_object* v_k_2260_, lean_object* v_cleanupAnnotations_2261_, lean_object* v_preserveNondepLet_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2268_; uint8_t v_preserveNondepLet_boxed_2269_; lean_object* v_res_2270_; 
v_cleanupAnnotations_boxed_2268_ = lean_unbox(v_cleanupAnnotations_2261_);
v_preserveNondepLet_boxed_2269_ = lean_unbox(v_preserveNondepLet_2262_);
v_res_2270_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2259_, v_k_2260_, v_cleanupAnnotations_boxed_2268_, v_preserveNondepLet_boxed_2269_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2271_, lean_object* v_e_2272_, lean_object* v_k_2273_, uint8_t v_cleanupAnnotations_2274_, uint8_t v_preserveNondepLet_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2272_, v_k_2273_, v_cleanupAnnotations_2274_, v_preserveNondepLet_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_e_2283_, lean_object* v_k_2284_, lean_object* v_cleanupAnnotations_2285_, lean_object* v_preserveNondepLet_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2292_; uint8_t v_preserveNondepLet_boxed_2293_; lean_object* v_res_2294_; 
v_cleanupAnnotations_boxed_2292_ = lean_unbox(v_cleanupAnnotations_2285_);
v_preserveNondepLet_boxed_2293_ = lean_unbox(v_preserveNondepLet_2286_);
v_res_2294_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2282_, v_e_2283_, v_k_2284_, v_cleanupAnnotations_boxed_2292_, v_preserveNondepLet_boxed_2293_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2295_, lean_object* v_e_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
v___x_2302_ = lean_infer_type(v_e_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = 0;
v___x_2305_ = 1;
v___x_2306_ = 1;
v___x_2307_ = l_Lean_Meta_mkForallFVars(v_xs_2295_, v_a_2303_, v___x_2304_, v___x_2305_, v___x_2304_, v___x_2306_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2307_;
}
else
{
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2308_, lean_object* v_e_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2308_, v_e_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_xs_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___f_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___f_2323_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2324_ = 0;
v___x_2325_ = 1;
v___x_2326_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2317_, v___f_2323_, v___x_2324_, v___x_2325_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2333_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2346_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2347_ = l_Lean_MessageData_ofName(v_mvarId_2340_);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2350_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2359_, lean_object* v_mvarId_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_mvarId_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2367_, v_mvarId_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_mctx_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_st_ref_get(v_a_2377_);
v_mctx_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_mctx_2382_);
lean_dec(v___x_2381_);
v___x_2383_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2382_, v_mvarId_2375_);
lean_dec_ref(v_mctx_2382_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
return v___x_2384_;
}
else
{
lean_object* v_val_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_mvarId_2375_);
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v___x_2383_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_val_2385_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_type_2389_; lean_object* v___x_2391_; 
v_type_2389_ = lean_ctor_get(v_val_2385_, 2);
lean_inc_ref(v_type_2389_);
lean_dec(v_val_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
lean_ctor_set(v___x_2387_, 0, v_type_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_type_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_lctx_2406_; lean_object* v___x_2407_; 
v_lctx_2406_ = lean_ctor_get(v_a_2402_, 2);
lean_inc(v_fvarId_2401_);
lean_inc_ref(v_lctx_2406_);
v___x_2407_ = lean_local_ctx_find(v_lctx_2406_, v_fvarId_2401_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2401_, v_a_2403_, v_a_2404_);
return v___x_2408_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_fvarId_2401_);
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2411_ = v___x_2407_;
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v___x_2407_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_LocalDecl_type(v_val_2409_);
lean_dec(v_val_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_a_2419_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2424_, v_a_2425_, v_a_2427_, v_a_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_instMonadEIO(lean_box(0));
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2440_ = l_StateRefT_x27_instMonad___redArg(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___f_2445_; 
v___x_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2445_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2445_, 0, v___x_2444_);
return v___f_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___f_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2447_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
return v___f_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; 
v___f_2448_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___f_2449_);
lean_ctor_set(v___x_2450_, 1, v___f_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___f_2452_; 
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2452_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2452_, 0, v___x_2451_);
return v___f_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___f_2454_; 
v___x_2453_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2454_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2454_, 0, v___x_2453_);
return v___f_2454_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; 
v___f_2455_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2456_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___f_2456_);
lean_ctor_set(v___x_2457_, 1, v___f_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2460_, lean_object* v_inferType_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
uint8_t v_cacheInferType_2506_; 
v_cacheInferType_2506_ = lean_ctor_get_uint8(v_a_2462_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2506_ == 0)
{
lean_dec_ref(v_e_2460_);
goto v___jp_2467_;
}
else
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_Expr_hasMVar(v_e_2460_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2460_, v_a_2462_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2608_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2608_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2608_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v_cache_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2603_; 
v___x_2513_ = lean_st_ref_get(v_a_2463_);
v_cache_2514_ = lean_ctor_get(v___x_2513_, 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; lean_object* v_unused_2605_; lean_object* v_unused_2606_; lean_object* v_unused_2607_; 
v_unused_2604_ = lean_ctor_get(v___x_2513_, 4);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v___x_2513_, 3);
lean_dec(v_unused_2605_);
v_unused_2606_ = lean_ctor_get(v___x_2513_, 2);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v___x_2513_, 0);
lean_dec(v_unused_2607_);
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2603_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_cache_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2603_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_inferType_2518_; lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v___x_2561_; 
v_inferType_2518_ = lean_ctor_get(v_cache_2514_, 0);
lean_inc_ref(v_inferType_2518_);
lean_dec_ref(v_cache_2514_);
v___f_2519_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2509_);
v___x_2561_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2519_, v___x_2520_, v_inferType_2518_, v_a_2509_);
lean_dec_ref(v_inferType_2518_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; lean_object* v_toApplicative_2563_; lean_object* v_toFunctor_2564_; lean_object* v_toSeq_2565_; lean_object* v_toSeqLeft_2566_; lean_object* v_toSeqRight_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___x_2577_; 
lean_del_object(v___x_2511_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2563_ = lean_ctor_get(v___x_2562_, 0);
v_toFunctor_2564_ = lean_ctor_get(v_toApplicative_2563_, 0);
v_toSeq_2565_ = lean_ctor_get(v_toApplicative_2563_, 2);
v_toSeqLeft_2566_ = lean_ctor_get(v_toApplicative_2563_, 3);
v_toSeqRight_2567_ = lean_ctor_get(v_toApplicative_2563_, 4);
v___f_2568_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2569_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2564_, 2);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toFunctor_2564_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toFunctor_2564_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___f_2570_);
lean_ctor_set(v___x_2572_, 1, v___f_2571_);
lean_inc(v_toSeqRight_2567_);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toSeqRight_2567_);
lean_inc(v_toSeqLeft_2566_);
v___f_2574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2574_, 0, v_toSeqLeft_2566_);
lean_inc(v_toSeq_2565_);
v___f_2575_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2575_, 0, v_toSeq_2565_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 4, v___f_2573_);
lean_ctor_set(v___x_2516_, 3, v___f_2574_);
lean_ctor_set(v___x_2516_, 2, v___f_2575_);
lean_ctor_set(v___x_2516_, 1, v___f_2568_);
lean_ctor_set(v___x_2516_, 0, v___x_2572_);
v___x_2577_ = v___x_2516_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___f_2568_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v___f_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___f_2574_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___f_2573_);
v___x_2577_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_toCold_2584_; lean_object* v_cancelTk_x3f_2585_; 
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___f_2569_);
v___x_2579_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2580_ = l_Lean_Core_instMonadRefCoreM;
v___x_2581_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2582_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2581_, v___x_2578_);
v___x_2583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2579_);
lean_ctor_set(v___x_2583_, 1, v___x_2580_);
lean_ctor_set(v___x_2583_, 2, v___x_2582_);
v_toCold_2584_ = lean_ctor_get(v_a_2464_, 0);
v_cancelTk_x3f_2585_ = lean_ctor_get(v_toCold_2584_, 3);
if (lean_obj_tag(v_cancelTk_x3f_2585_) == 1)
{
lean_object* v_val_2586_; uint8_t v___x_2587_; 
v_val_2586_ = lean_ctor_get(v_cancelTk_x3f_2585_, 0);
v___x_2587_ = l_IO_CancelToken_isSet(v_val_2586_);
if (v___x_2587_ == 0)
{
lean_dec_ref_known(v___x_2583_, 3);
goto v___jp_2521_;
}
else
{
lean_object* v___x_1999__overap_2588_; lean_object* v___x_2589_; 
v___x_1999__overap_2588_ = l_Lean_throwInterruptException___redArg(v___x_2583_);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
v___x_2589_ = lean_apply_3(v___x_1999__overap_2588_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
goto v___jp_2521_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_inferType_2461_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2583_, 3);
goto v___jp_2521_;
}
}
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2601_; 
lean_del_object(v___x_2516_);
lean_dec(v_a_2509_);
lean_dec_ref(v_inferType_2461_);
v_val_2599_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2561_, 1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_val_2599_);
v___x_2601_ = v___x_2511_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_val_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
v___jp_2521_:
{
lean_object* v___x_2522_; 
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2522_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; uint8_t v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
v___x_2524_ = l_Lean_Expr_hasMVar(v_a_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2559_; 
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2522_, 0);
lean_dec(v_unused_2560_);
v___x_2526_ = v___x_2522_;
v_isShared_2527_ = v_isSharedCheck_2559_;
goto v_resetjp_2525_;
}
else
{
lean_dec(v___x_2522_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2559_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v_cache_2529_; lean_object* v_mctx_2530_; lean_object* v_zetaDeltaFVarIds_2531_; lean_object* v_postponed_2532_; lean_object* v_diag_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2558_; 
v___x_2528_ = lean_st_ref_take(v_a_2463_);
v_cache_2529_ = lean_ctor_get(v___x_2528_, 1);
v_mctx_2530_ = lean_ctor_get(v___x_2528_, 0);
v_zetaDeltaFVarIds_2531_ = lean_ctor_get(v___x_2528_, 2);
v_postponed_2532_ = lean_ctor_get(v___x_2528_, 3);
v_diag_2533_ = lean_ctor_get(v___x_2528_, 4);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2535_ = v___x_2528_;
v_isShared_2536_ = v_isSharedCheck_2558_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_diag_2533_);
lean_inc(v_postponed_2532_);
lean_inc(v_zetaDeltaFVarIds_2531_);
lean_inc(v_cache_2529_);
lean_inc(v_mctx_2530_);
lean_dec(v___x_2528_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2558_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_inferType_2537_; lean_object* v_funInfo_2538_; lean_object* v_synthInstance_2539_; lean_object* v_whnf_2540_; lean_object* v_defEqTrans_2541_; lean_object* v_defEqPerm_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2557_; 
v_inferType_2537_ = lean_ctor_get(v_cache_2529_, 0);
v_funInfo_2538_ = lean_ctor_get(v_cache_2529_, 1);
v_synthInstance_2539_ = lean_ctor_get(v_cache_2529_, 2);
v_whnf_2540_ = lean_ctor_get(v_cache_2529_, 3);
v_defEqTrans_2541_ = lean_ctor_get(v_cache_2529_, 4);
v_defEqPerm_2542_ = lean_ctor_get(v_cache_2529_, 5);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_cache_2529_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2544_ = v_cache_2529_;
v_isShared_2545_ = v_isSharedCheck_2557_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_defEqPerm_2542_);
lean_inc(v_defEqTrans_2541_);
lean_inc(v_whnf_2540_);
lean_inc(v_synthInstance_2539_);
lean_inc(v_funInfo_2538_);
lean_inc(v_inferType_2537_);
lean_dec(v_cache_2529_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2557_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_inc(v_a_2523_);
v___x_2546_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2519_, v___x_2520_, v_inferType_2537_, v_a_2509_, v_a_2523_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_funInfo_2538_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_synthInstance_2539_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_whnf_2540_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_defEqTrans_2541_);
lean_ctor_set(v_reuseFailAlloc_2556_, 5, v_defEqPerm_2542_);
v___x_2548_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v___x_2548_);
v___x_2550_ = v___x_2535_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_mctx_2530_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_zetaDeltaFVarIds_2531_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_postponed_2532_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_diag_2533_);
v___x_2550_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_st_ref_put(v_a_2463_, v___x_2550_);
if (v_isShared_2527_ == 0)
{
v___x_2553_ = v___x_2526_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2523_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2523_);
lean_dec(v_a_2509_);
return v___x_2522_;
}
}
else
{
lean_dec(v_a_2509_);
return v___x_2522_;
}
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v_inferType_2461_);
v_a_2609_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2508_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2508_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_dec_ref(v_e_2460_);
goto v___jp_2467_;
}
}
v___jp_2467_:
{
lean_object* v___x_2468_; lean_object* v_toApplicative_2469_; lean_object* v_toFunctor_2470_; lean_object* v_toSeq_2471_; lean_object* v_toSeqLeft_2472_; lean_object* v_toSeqRight_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_toCold_2489_; lean_object* v_cancelTk_x3f_2490_; 
v___x_2468_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2469_ = lean_ctor_get(v___x_2468_, 0);
v_toFunctor_2470_ = lean_ctor_get(v_toApplicative_2469_, 0);
v_toSeq_2471_ = lean_ctor_get(v_toApplicative_2469_, 2);
v_toSeqLeft_2472_ = lean_ctor_get(v_toApplicative_2469_, 3);
v_toSeqRight_2473_ = lean_ctor_get(v_toApplicative_2469_, 4);
v___f_2474_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2475_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2470_, 2);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toFunctor_2470_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toFunctor_2470_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___f_2476_);
lean_ctor_set(v___x_2478_, 1, v___f_2477_);
lean_inc(v_toSeqRight_2473_);
v___f_2479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2479_, 0, v_toSeqRight_2473_);
lean_inc(v_toSeqLeft_2472_);
v___f_2480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2480_, 0, v_toSeqLeft_2472_);
lean_inc(v_toSeq_2471_);
v___f_2481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2481_, 0, v_toSeq_2471_);
v___x_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2478_);
lean_ctor_set(v___x_2482_, 1, v___f_2474_);
lean_ctor_set(v___x_2482_, 2, v___f_2481_);
lean_ctor_set(v___x_2482_, 3, v___f_2480_);
lean_ctor_set(v___x_2482_, 4, v___f_2479_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___f_2475_);
v___x_2484_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2485_ = l_Lean_Core_instMonadRefCoreM;
v___x_2486_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2487_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2486_, v___x_2483_);
v___x_2488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2484_);
lean_ctor_set(v___x_2488_, 1, v___x_2485_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
v_toCold_2489_ = lean_ctor_get(v_a_2464_, 0);
v_cancelTk_x3f_2490_ = lean_ctor_get(v_toCold_2489_, 3);
if (lean_obj_tag(v_cancelTk_x3f_2490_) == 1)
{
lean_object* v_val_2491_; uint8_t v___x_2492_; 
v_val_2491_ = lean_ctor_get(v_cancelTk_x3f_2490_, 0);
v___x_2492_ = l_IO_CancelToken_isSet(v_val_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec_ref_known(v___x_2488_, 3);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2493_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2493_;
}
else
{
lean_object* v___x_1711__overap_2494_; lean_object* v___x_2495_; 
v___x_1711__overap_2494_ = l_Lean_throwInterruptException___redArg(v___x_2488_);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
v___x_2495_ = lean_apply_3(v___x_1711__overap_2494_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2495_, 1);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2496_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2496_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v_inferType_2461_);
v_a_2497_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2495_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; 
lean_dec_ref_known(v___x_2488_, 3);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2505_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2617_, lean_object* v_inferType_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2617_, v_inferType_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = 2;
v___x_2626_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2679_; uint8_t v_beta_2680_; 
v___x_2679_ = l_Lean_Meta_Context_config(v___y_2628_);
v_beta_2680_ = lean_ctor_get_uint8(v___x_2679_, 13);
if (v_beta_2680_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2633_;
}
else
{
uint8_t v_iota_2681_; 
v_iota_2681_ = lean_ctor_get_uint8(v___x_2679_, 12);
if (v_iota_2681_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2633_;
}
else
{
uint8_t v_zeta_2682_; 
v_zeta_2682_ = lean_ctor_get_uint8(v___x_2679_, 15);
if (v_zeta_2682_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2633_;
}
else
{
uint8_t v_zetaHave_2683_; 
v_zetaHave_2683_ = lean_ctor_get_uint8(v___x_2679_, 18);
if (v_zetaHave_2683_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2633_;
}
else
{
uint8_t v_zetaDelta_2684_; 
v_zetaDelta_2684_ = lean_ctor_get_uint8(v___x_2679_, 16);
if (v_zetaDelta_2684_ == 0)
{
lean_dec_ref(v___x_2679_);
goto v___jp_2633_;
}
else
{
uint8_t v_etaStruct_2685_; uint8_t v_proj_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_etaStruct_2685_ = lean_ctor_get_uint8(v___x_2679_, 10);
v_proj_2686_ = lean_ctor_get_uint8(v___x_2679_, 14);
lean_dec_ref(v___x_2679_);
v___x_2687_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2686_);
v___x_2688_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_2689_ = lean_nat_dec_eq(v___x_2687_, v___x_2688_);
lean_dec(v___x_2687_);
if (v___x_2689_ == 0)
{
goto v___jp_2633_;
}
else
{
uint8_t v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = 0;
v___x_2691_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2685_, v___x_2690_);
if (v___x_2691_ == 0)
{
goto v___jp_2633_;
}
else
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_apply_5(v_x_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, lean_box(0));
return v___x_2692_;
}
}
}
}
}
}
}
v___jp_2633_:
{
lean_object* v___x_2634_; uint8_t v_foApprox_2635_; uint8_t v_ctxApprox_2636_; uint8_t v_quasiPatternApprox_2637_; uint8_t v_constApprox_2638_; uint8_t v_isDefEqStuckEx_2639_; uint8_t v_unificationHints_2640_; uint8_t v_proofIrrelevance_2641_; uint8_t v_assignSyntheticOpaque_2642_; uint8_t v_offsetCnstrs_2643_; uint8_t v_transparency_2644_; uint8_t v_univApprox_2645_; uint8_t v_zetaUnused_2646_; uint8_t v_canUnfoldPredicateConfig_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2678_; 
v___x_2634_ = l_Lean_Meta_Context_config(v___y_2628_);
v_foApprox_2635_ = lean_ctor_get_uint8(v___x_2634_, 0);
v_ctxApprox_2636_ = lean_ctor_get_uint8(v___x_2634_, 1);
v_quasiPatternApprox_2637_ = lean_ctor_get_uint8(v___x_2634_, 2);
v_constApprox_2638_ = lean_ctor_get_uint8(v___x_2634_, 3);
v_isDefEqStuckEx_2639_ = lean_ctor_get_uint8(v___x_2634_, 4);
v_unificationHints_2640_ = lean_ctor_get_uint8(v___x_2634_, 5);
v_proofIrrelevance_2641_ = lean_ctor_get_uint8(v___x_2634_, 6);
v_assignSyntheticOpaque_2642_ = lean_ctor_get_uint8(v___x_2634_, 7);
v_offsetCnstrs_2643_ = lean_ctor_get_uint8(v___x_2634_, 8);
v_transparency_2644_ = lean_ctor_get_uint8(v___x_2634_, 9);
v_univApprox_2645_ = lean_ctor_get_uint8(v___x_2634_, 11);
v_zetaUnused_2646_ = lean_ctor_get_uint8(v___x_2634_, 17);
v_canUnfoldPredicateConfig_2647_ = lean_ctor_get_uint8(v___x_2634_, 19);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2649_ = v___x_2634_;
v_isShared_2650_ = v_isSharedCheck_2678_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2634_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2678_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v___x_2651_; uint8_t v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2655_; 
v___x_2651_ = 1;
v___x_2652_ = 0;
v___x_2653_ = 2;
if (v_isShared_2650_ == 0)
{
v___x_2655_ = v___x_2649_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 0, v_foApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 1, v_ctxApprox_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 2, v_quasiPatternApprox_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 3, v_constApprox_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 4, v_isDefEqStuckEx_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 5, v_unificationHints_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 6, v_proofIrrelevance_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 7, v_assignSyntheticOpaque_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 8, v_offsetCnstrs_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 9, v_transparency_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 11, v_univApprox_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 17, v_zetaUnused_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, 19, v_canUnfoldPredicateConfig_2647_);
v___x_2655_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
uint8_t v_trackZetaDelta_2656_; lean_object* v_zetaDeltaSet_2657_; lean_object* v_lctx_2658_; lean_object* v_localInstances_2659_; lean_object* v_defEqCtx_x3f_2660_; lean_object* v_synthPendingDepth_2661_; lean_object* v_customCanUnfoldPredicate_x3f_2662_; uint8_t v_univApprox_2663_; uint8_t v_inTypeClassResolution_2664_; uint8_t v_cacheInferType_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2675_; 
lean_ctor_set_uint8(v___x_2655_, 10, v___x_2652_);
lean_ctor_set_uint8(v___x_2655_, 12, v___x_2651_);
lean_ctor_set_uint8(v___x_2655_, 13, v___x_2651_);
lean_ctor_set_uint8(v___x_2655_, 14, v___x_2653_);
lean_ctor_set_uint8(v___x_2655_, 15, v___x_2651_);
lean_ctor_set_uint8(v___x_2655_, 16, v___x_2651_);
lean_ctor_set_uint8(v___x_2655_, 18, v___x_2651_);
v_trackZetaDelta_2656_ = lean_ctor_get_uint8(v___y_2628_, sizeof(void*)*7);
v_zetaDeltaSet_2657_ = lean_ctor_get(v___y_2628_, 1);
v_lctx_2658_ = lean_ctor_get(v___y_2628_, 2);
v_localInstances_2659_ = lean_ctor_get(v___y_2628_, 3);
v_defEqCtx_x3f_2660_ = lean_ctor_get(v___y_2628_, 4);
v_synthPendingDepth_2661_ = lean_ctor_get(v___y_2628_, 5);
v_customCanUnfoldPredicate_x3f_2662_ = lean_ctor_get(v___y_2628_, 6);
v_univApprox_2663_ = lean_ctor_get_uint8(v___y_2628_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2664_ = lean_ctor_get_uint8(v___y_2628_, sizeof(void*)*7 + 2);
v_cacheInferType_2665_ = lean_ctor_get_uint8(v___y_2628_, sizeof(void*)*7 + 3);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___y_2628_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___y_2628_, 0);
lean_dec(v_unused_2676_);
v___x_2667_ = v___y_2628_;
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2662_);
lean_inc(v_synthPendingDepth_2661_);
lean_inc(v_defEqCtx_x3f_2660_);
lean_inc(v_localInstances_2659_);
lean_inc(v_lctx_2658_);
lean_inc(v_zetaDeltaSet_2657_);
lean_dec(v___y_2628_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2675_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint64_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2655_);
v___x_2670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2670_, 0, v___x_2655_);
lean_ctor_set_uint64(v___x_2670_, sizeof(void*)*1, v___x_2669_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_zetaDeltaSet_2657_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_lctx_2658_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_localInstances_2659_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_defEqCtx_x3f_2660_);
lean_ctor_set(v_reuseFailAlloc_2674_, 5, v_synthPendingDepth_2661_);
lean_ctor_set(v_reuseFailAlloc_2674_, 6, v_customCanUnfoldPredicate_x3f_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, sizeof(void*)*7, v_trackZetaDelta_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, sizeof(void*)*7 + 1, v_univApprox_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, sizeof(void*)*7 + 3, v_cacheInferType_2665_);
v___x_2672_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_apply_5(v_x_2627_, v___x_2672_, v___y_2629_, v___y_2630_, v___y_2631_, lean_box(0));
return v___x_2673_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___y_2707_; lean_object* v___x_2724_; uint8_t v_transparency_2725_; uint8_t v___x_2726_; uint8_t v___x_2727_; 
v___x_2724_ = l_Lean_Meta_Context_config(v_a_2701_);
v_transparency_2725_ = lean_ctor_get_uint8(v___x_2724_, 9);
lean_dec_ref(v___x_2724_);
v___x_2726_ = 1;
v___x_2727_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
lean_inc(v_a_2704_);
lean_inc_ref(v_a_2703_);
lean_inc(v_a_2702_);
lean_inc_ref(v_a_2701_);
v___x_2728_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
v___y_2707_ = v___x_2728_;
goto v___jp_2706_;
}
else
{
lean_object* v_keyedConfig_2729_; uint8_t v_trackZetaDelta_2730_; lean_object* v_zetaDeltaSet_2731_; lean_object* v_lctx_2732_; lean_object* v_localInstances_2733_; lean_object* v_defEqCtx_x3f_2734_; lean_object* v_synthPendingDepth_2735_; lean_object* v_customCanUnfoldPredicate_x3f_2736_; uint8_t v_univApprox_2737_; uint8_t v_inTypeClassResolution_2738_; uint8_t v_cacheInferType_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_keyedConfig_2729_ = lean_ctor_get(v_a_2701_, 0);
v_trackZetaDelta_2730_ = lean_ctor_get_uint8(v_a_2701_, sizeof(void*)*7);
v_zetaDeltaSet_2731_ = lean_ctor_get(v_a_2701_, 1);
v_lctx_2732_ = lean_ctor_get(v_a_2701_, 2);
v_localInstances_2733_ = lean_ctor_get(v_a_2701_, 3);
v_defEqCtx_x3f_2734_ = lean_ctor_get(v_a_2701_, 4);
v_synthPendingDepth_2735_ = lean_ctor_get(v_a_2701_, 5);
v_customCanUnfoldPredicate_x3f_2736_ = lean_ctor_get(v_a_2701_, 6);
v_univApprox_2737_ = lean_ctor_get_uint8(v_a_2701_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2738_ = lean_ctor_get_uint8(v_a_2701_, sizeof(void*)*7 + 2);
v_cacheInferType_2739_ = lean_ctor_get_uint8(v_a_2701_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2729_);
v___x_2740_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2726_, v_keyedConfig_2729_);
lean_inc(v_customCanUnfoldPredicate_x3f_2736_);
lean_inc(v_synthPendingDepth_2735_);
lean_inc(v_defEqCtx_x3f_2734_);
lean_inc_ref(v_localInstances_2733_);
lean_inc_ref(v_lctx_2732_);
lean_inc(v_zetaDeltaSet_2731_);
v___x_2741_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_zetaDeltaSet_2731_);
lean_ctor_set(v___x_2741_, 2, v_lctx_2732_);
lean_ctor_set(v___x_2741_, 3, v_localInstances_2733_);
lean_ctor_set(v___x_2741_, 4, v_defEqCtx_x3f_2734_);
lean_ctor_set(v___x_2741_, 5, v_synthPendingDepth_2735_);
lean_ctor_set(v___x_2741_, 6, v_customCanUnfoldPredicate_x3f_2736_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*7, v_trackZetaDelta_2730_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*7 + 1, v_univApprox_2737_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2738_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*7 + 3, v_cacheInferType_2739_);
lean_inc(v_a_2704_);
lean_inc_ref(v_a_2703_);
lean_inc(v_a_2702_);
v___x_2742_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2700_, v___x_2741_, v_a_2702_, v_a_2703_, v_a_2704_);
v___y_2707_ = v___x_2742_;
goto v___jp_2706_;
}
v___jp_2706_:
{
if (lean_obj_tag(v___y_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___y_2707_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___y_2707_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___y_2707_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___y_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___y_2707_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___y_2707_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___y_2707_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___y_2707_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2750_, lean_object* v_x_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___y_2758_; lean_object* v___x_2775_; uint8_t v_transparency_2776_; uint8_t v___x_2777_; uint8_t v___x_2778_; 
v___x_2775_ = l_Lean_Meta_Context_config(v_a_2752_);
v_transparency_2776_ = lean_ctor_get_uint8(v___x_2775_, 9);
lean_dec_ref(v___x_2775_);
v___x_2777_ = 1;
v___x_2778_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2776_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
v___x_2779_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
v___y_2758_ = v___x_2779_;
goto v___jp_2757_;
}
else
{
lean_object* v_keyedConfig_2780_; uint8_t v_trackZetaDelta_2781_; lean_object* v_zetaDeltaSet_2782_; lean_object* v_lctx_2783_; lean_object* v_localInstances_2784_; lean_object* v_defEqCtx_x3f_2785_; lean_object* v_synthPendingDepth_2786_; lean_object* v_customCanUnfoldPredicate_x3f_2787_; uint8_t v_univApprox_2788_; uint8_t v_inTypeClassResolution_2789_; uint8_t v_cacheInferType_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_keyedConfig_2780_ = lean_ctor_get(v_a_2752_, 0);
v_trackZetaDelta_2781_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7);
v_zetaDeltaSet_2782_ = lean_ctor_get(v_a_2752_, 1);
v_lctx_2783_ = lean_ctor_get(v_a_2752_, 2);
v_localInstances_2784_ = lean_ctor_get(v_a_2752_, 3);
v_defEqCtx_x3f_2785_ = lean_ctor_get(v_a_2752_, 4);
v_synthPendingDepth_2786_ = lean_ctor_get(v_a_2752_, 5);
v_customCanUnfoldPredicate_x3f_2787_ = lean_ctor_get(v_a_2752_, 6);
v_univApprox_2788_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2789_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 2);
v_cacheInferType_2790_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2780_);
v___x_2791_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2777_, v_keyedConfig_2780_);
lean_inc(v_customCanUnfoldPredicate_x3f_2787_);
lean_inc(v_synthPendingDepth_2786_);
lean_inc(v_defEqCtx_x3f_2785_);
lean_inc_ref(v_localInstances_2784_);
lean_inc_ref(v_lctx_2783_);
lean_inc(v_zetaDeltaSet_2782_);
v___x_2792_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v_zetaDeltaSet_2782_);
lean_ctor_set(v___x_2792_, 2, v_lctx_2783_);
lean_ctor_set(v___x_2792_, 3, v_localInstances_2784_);
lean_ctor_set(v___x_2792_, 4, v_defEqCtx_x3f_2785_);
lean_ctor_set(v___x_2792_, 5, v_synthPendingDepth_2786_);
lean_ctor_set(v___x_2792_, 6, v_customCanUnfoldPredicate_x3f_2787_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7, v_trackZetaDelta_2781_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 1, v_univApprox_2788_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2789_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 3, v_cacheInferType_2790_);
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
v___x_2793_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2751_, v___x_2792_, v_a_2753_, v_a_2754_, v_a_2755_);
v___y_2758_ = v___x_2793_;
goto v___jp_2757_;
}
v___jp_2757_:
{
if (lean_obj_tag(v___y_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
v_a_2759_ = lean_ctor_get(v___y_2758_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___y_2758_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___y_2758_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___y_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___y_2758_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___y_2758_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___y_2758_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___y_2758_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2794_, lean_object* v_x_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2794_, v_x_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
return v_res_2801_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_box(0);
v___x_2803_ = l_Lean_interruptExceptionId;
v___x_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v_ks_2824_; lean_object* v_vs_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2854_; 
v_ks_2824_ = lean_ctor_get(v_x_2820_, 0);
v_vs_2825_ = lean_ctor_get(v_x_2820_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_x_2820_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2827_ = v_x_2820_;
v_isShared_2828_ = v_isSharedCheck_2854_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_vs_2825_);
lean_inc(v_ks_2824_);
lean_dec(v_x_2820_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2854_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
uint8_t v___y_2830_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = lean_array_get_size(v_ks_2824_);
v___x_2843_ = lean_nat_dec_lt(v_x_2821_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_del_object(v___x_2827_);
lean_dec(v_x_2821_);
v___x_2844_ = lean_array_push(v_ks_2824_, v_x_2822_);
v___x_2845_ = lean_array_push(v_vs_2825_, v_x_2823_);
v___x_2846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
return v___x_2846_;
}
else
{
lean_object* v_expr_2847_; uint64_t v_configKey_2848_; lean_object* v_k_x27_2849_; lean_object* v_expr_2850_; uint64_t v_configKey_2851_; uint8_t v___x_2852_; 
v_expr_2847_ = lean_ctor_get(v_x_2822_, 0);
v_configKey_2848_ = lean_ctor_get_uint64(v_x_2822_, sizeof(void*)*1);
v_k_x27_2849_ = lean_array_fget_borrowed(v_ks_2824_, v_x_2821_);
v_expr_2850_ = lean_ctor_get(v_k_x27_2849_, 0);
v_configKey_2851_ = lean_ctor_get_uint64(v_k_x27_2849_, sizeof(void*)*1);
v___x_2852_ = lean_expr_equal(v_expr_2847_, v_expr_2850_);
if (v___x_2852_ == 0)
{
v___y_2830_ = v___x_2852_;
goto v___jp_2829_;
}
else
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_uint64_dec_eq(v_configKey_2848_, v_configKey_2851_);
v___y_2830_ = v___x_2853_;
goto v___jp_2829_;
}
}
v___jp_2829_:
{
if (v___y_2830_ == 0)
{
lean_object* v___x_2832_; 
if (v_isShared_2828_ == 0)
{
v___x_2832_ = v___x_2827_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_ks_2824_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_vs_2825_);
v___x_2832_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_x_2821_, v___x_2833_);
lean_dec(v_x_2821_);
v_x_2820_ = v___x_2832_;
v_x_2821_ = v___x_2834_;
goto _start;
}
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2837_ = lean_array_fset(v_ks_2824_, v_x_2821_, v_x_2822_);
v___x_2838_ = lean_array_fset(v_vs_2825_, v_x_2821_, v_x_2823_);
lean_dec(v_x_2821_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 1, v___x_2838_);
lean_ctor_set(v___x_2827_, 0, v___x_2837_);
v___x_2840_ = v___x_2827_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2855_, lean_object* v_k_2856_, lean_object* v_v_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2855_, v___x_2858_, v_k_2856_, v_v_2857_);
return v___x_2859_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2861_, size_t v_x_2862_, size_t v_x_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
lean_object* v_es_2866_; size_t v___x_2867_; size_t v___x_2868_; lean_object* v_j_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v_es_2866_ = lean_ctor_get(v_x_2861_, 0);
v___x_2867_ = ((size_t)31ULL);
v___x_2868_ = lean_usize_land(v_x_2862_, v___x_2867_);
v_j_2869_ = lean_usize_to_nat(v___x_2868_);
v___x_2870_ = lean_array_get_size(v_es_2866_);
v___x_2871_ = lean_nat_dec_lt(v_j_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_dec(v_j_2869_);
lean_dec(v_x_2865_);
lean_dec_ref(v_x_2864_);
return v_x_2861_;
}
else
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2917_; 
lean_inc_ref(v_es_2866_);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v_x_2861_, 0);
lean_dec(v_unused_2918_);
v___x_2873_ = v_x_2861_;
v_isShared_2874_ = v_isSharedCheck_2917_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v_x_2861_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2917_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v_v_2875_; lean_object* v___x_2876_; lean_object* v_xs_x27_2877_; lean_object* v___y_2879_; 
v_v_2875_ = lean_array_fget(v_es_2866_, v_j_2869_);
v___x_2876_ = lean_box(0);
v_xs_x27_2877_ = lean_array_fset(v_es_2866_, v_j_2869_, v___x_2876_);
switch(lean_obj_tag(v_v_2875_))
{
case 0:
{
lean_object* v_key_2884_; lean_object* v_val_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2902_; 
v_key_2884_ = lean_ctor_get(v_v_2875_, 0);
v_val_2885_ = lean_ctor_get(v_v_2875_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_v_2875_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2887_ = v_v_2875_;
v_isShared_2888_ = v_isSharedCheck_2902_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_val_2885_);
lean_inc(v_key_2884_);
lean_dec(v_v_2875_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2902_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
uint8_t v___y_2890_; lean_object* v_expr_2896_; uint64_t v_configKey_2897_; lean_object* v_expr_2898_; uint64_t v_configKey_2899_; uint8_t v___x_2900_; 
v_expr_2896_ = lean_ctor_get(v_x_2864_, 0);
v_configKey_2897_ = lean_ctor_get_uint64(v_x_2864_, sizeof(void*)*1);
v_expr_2898_ = lean_ctor_get(v_key_2884_, 0);
v_configKey_2899_ = lean_ctor_get_uint64(v_key_2884_, sizeof(void*)*1);
v___x_2900_ = lean_expr_equal(v_expr_2896_, v_expr_2898_);
if (v___x_2900_ == 0)
{
v___y_2890_ = v___x_2900_;
goto v___jp_2889_;
}
else
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_uint64_dec_eq(v_configKey_2897_, v_configKey_2899_);
v___y_2890_ = v___x_2901_;
goto v___jp_2889_;
}
v___jp_2889_:
{
if (v___y_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_del_object(v___x_2887_);
v___x_2891_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2884_, v_val_2885_, v_x_2864_, v_x_2865_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___y_2879_ = v___x_2892_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_val_2885_);
lean_dec(v_key_2884_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v_x_2865_);
lean_ctor_set(v___x_2887_, 0, v_x_2864_);
v___x_2894_ = v___x_2887_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_x_2864_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_x_2865_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v___y_2879_ = v___x_2894_;
goto v___jp_2878_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2915_; 
v_node_2903_ = lean_ctor_get(v_v_2875_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_v_2875_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2905_ = v_v_2875_;
v_isShared_2906_ = v_isSharedCheck_2915_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_node_2903_);
lean_dec(v_v_2875_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2915_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
size_t v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2907_ = ((size_t)5ULL);
v___x_2908_ = lean_usize_shift_right(v_x_2862_, v___x_2907_);
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_x_2863_, v___x_2909_);
v___x_2911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2903_, v___x_2908_, v___x_2910_, v_x_2864_, v_x_2865_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2911_);
v___x_2913_ = v___x_2905_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
v___y_2879_ = v___x_2913_;
goto v___jp_2878_;
}
}
}
default: 
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v_x_2864_);
lean_ctor_set(v___x_2916_, 1, v_x_2865_);
v___y_2879_ = v___x_2916_;
goto v___jp_2878_;
}
}
v___jp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_array_fset(v_xs_x27_2877_, v_j_2869_, v___y_2879_);
lean_dec(v_j_2869_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2880_);
v___x_2882_ = v___x_2873_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
else
{
lean_object* v_ks_2919_; lean_object* v_vs_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2938_; 
v_ks_2919_ = lean_ctor_get(v_x_2861_, 0);
v_vs_2920_ = lean_ctor_get(v_x_2861_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2922_ = v_x_2861_;
v_isShared_2923_ = v_isSharedCheck_2938_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_vs_2920_);
lean_inc(v_ks_2919_);
lean_dec(v_x_2861_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2938_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_ks_2919_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_vs_2920_);
v___x_2925_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v_newNode_2926_; size_t v___x_2927_; uint8_t v___x_2928_; 
v_newNode_2926_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2925_, v_x_2864_, v_x_2865_);
v___x_2927_ = ((size_t)7ULL);
v___x_2928_ = lean_usize_dec_le(v___x_2927_, v_x_2863_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2926_);
v___x_2930_ = lean_unsigned_to_nat(4u);
v___x_2931_ = lean_nat_dec_lt(v___x_2929_, v___x_2930_);
lean_dec(v___x_2929_);
if (v___x_2931_ == 0)
{
lean_object* v_ks_2932_; lean_object* v_vs_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_ks_2932_ = lean_ctor_get(v_newNode_2926_, 0);
lean_inc_ref(v_ks_2932_);
v_vs_2933_ = lean_ctor_get(v_newNode_2926_, 1);
lean_inc_ref(v_vs_2933_);
lean_dec_ref(v_newNode_2926_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2863_, v_ks_2932_, v_vs_2933_, v___x_2934_, v___x_2935_);
lean_dec_ref(v_vs_2933_);
lean_dec_ref(v_ks_2932_);
return v___x_2936_;
}
else
{
return v_newNode_2926_;
}
}
else
{
return v_newNode_2926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2939_, lean_object* v_keys_2940_, lean_object* v_vals_2941_, lean_object* v_i_2942_, lean_object* v_entries_2943_){
_start:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_keys_2940_);
v___x_2945_ = lean_nat_dec_lt(v_i_2942_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec(v_i_2942_);
return v_entries_2943_;
}
else
{
lean_object* v_k_2946_; lean_object* v_expr_2947_; uint64_t v_configKey_2948_; lean_object* v_v_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; size_t v_h_2952_; size_t v___x_2953_; lean_object* v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v_h_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_k_2946_ = lean_array_fget_borrowed(v_keys_2940_, v_i_2942_);
v_expr_2947_ = lean_ctor_get(v_k_2946_, 0);
v_configKey_2948_ = lean_ctor_get_uint64(v_k_2946_, sizeof(void*)*1);
v_v_2949_ = lean_array_fget_borrowed(v_vals_2941_, v_i_2942_);
v___x_2950_ = l_Lean_Expr_hash(v_expr_2947_);
v___x_2951_ = lean_uint64_mix_hash(v___x_2950_, v_configKey_2948_);
v_h_2952_ = lean_uint64_to_usize(v___x_2951_);
v___x_2953_ = ((size_t)5ULL);
v___x_2954_ = lean_unsigned_to_nat(1u);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_sub(v_depth_2939_, v___x_2955_);
v___x_2957_ = lean_usize_mul(v___x_2953_, v___x_2956_);
v_h_2958_ = lean_usize_shift_right(v_h_2952_, v___x_2957_);
v___x_2959_ = lean_nat_add(v_i_2942_, v___x_2954_);
lean_dec(v_i_2942_);
lean_inc(v_v_2949_);
lean_inc(v_k_2946_);
v___x_2960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2943_, v_h_2958_, v_depth_2939_, v_k_2946_, v_v_2949_);
v_i_2942_ = v___x_2959_;
v_entries_2943_ = v___x_2960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2962_, lean_object* v_keys_2963_, lean_object* v_vals_2964_, lean_object* v_i_2965_, lean_object* v_entries_2966_){
_start:
{
size_t v_depth_boxed_2967_; lean_object* v_res_2968_; 
v_depth_boxed_2967_ = lean_unbox_usize(v_depth_2962_);
lean_dec(v_depth_2962_);
v_res_2968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2967_, v_keys_2963_, v_vals_2964_, v_i_2965_, v_entries_2966_);
lean_dec_ref(v_vals_2964_);
lean_dec_ref(v_keys_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_){
_start:
{
size_t v_x_2785__boxed_2974_; size_t v_x_2786__boxed_2975_; lean_object* v_res_2976_; 
v_x_2785__boxed_2974_ = lean_unbox_usize(v_x_2970_);
lean_dec(v_x_2970_);
v_x_2786__boxed_2975_ = lean_unbox_usize(v_x_2971_);
lean_dec(v_x_2971_);
v_res_2976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2969_, v_x_2785__boxed_2974_, v_x_2786__boxed_2975_, v_x_2972_, v_x_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2977_, lean_object* v_x_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v_expr_2980_; uint64_t v_configKey_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v_expr_2980_ = lean_ctor_get(v_x_2978_, 0);
v_configKey_2981_ = lean_ctor_get_uint64(v_x_2978_, sizeof(void*)*1);
v___x_2982_ = l_Lean_Expr_hash(v_expr_2980_);
v___x_2983_ = lean_uint64_mix_hash(v___x_2982_, v_configKey_2981_);
v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2977_, v___x_2984_, v___x_2985_, v_x_2978_, v_x_2979_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2987_, lean_object* v_vals_2988_, lean_object* v_i_2989_, lean_object* v_k_2990_){
_start:
{
uint8_t v___y_2992_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = lean_array_get_size(v_keys_2987_);
v___x_2999_ = lean_nat_dec_lt(v_i_2989_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_i_2989_);
v___x_3000_ = lean_box(0);
return v___x_3000_;
}
else
{
lean_object* v_expr_3001_; uint64_t v_configKey_3002_; lean_object* v_k_x27_3003_; lean_object* v_expr_3004_; uint64_t v_configKey_3005_; uint8_t v___x_3006_; 
v_expr_3001_ = lean_ctor_get(v_k_2990_, 0);
v_configKey_3002_ = lean_ctor_get_uint64(v_k_2990_, sizeof(void*)*1);
v_k_x27_3003_ = lean_array_fget_borrowed(v_keys_2987_, v_i_2989_);
v_expr_3004_ = lean_ctor_get(v_k_x27_3003_, 0);
v_configKey_3005_ = lean_ctor_get_uint64(v_k_x27_3003_, sizeof(void*)*1);
v___x_3006_ = lean_expr_equal(v_expr_3001_, v_expr_3004_);
if (v___x_3006_ == 0)
{
v___y_2992_ = v___x_3006_;
goto v___jp_2991_;
}
else
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_uint64_dec_eq(v_configKey_3002_, v_configKey_3005_);
v___y_2992_ = v___x_3007_;
goto v___jp_2991_;
}
}
v___jp_2991_:
{
if (v___y_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_unsigned_to_nat(1u);
v___x_2994_ = lean_nat_add(v_i_2989_, v___x_2993_);
lean_dec(v_i_2989_);
v_i_2989_ = v___x_2994_;
goto _start;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_array_fget_borrowed(v_vals_2988_, v_i_2989_);
lean_dec(v_i_2989_);
lean_inc(v___x_2996_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3008_, lean_object* v_vals_3009_, lean_object* v_i_3010_, lean_object* v_k_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3008_, v_vals_3009_, v_i_3010_, v_k_3011_);
lean_dec_ref(v_k_3011_);
lean_dec_ref(v_vals_3009_);
lean_dec_ref(v_keys_3008_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3013_, size_t v_x_3014_, lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3013_) == 0)
{
lean_object* v_es_3016_; lean_object* v___x_3017_; size_t v___x_3018_; size_t v___x_3019_; lean_object* v_j_3020_; lean_object* v___x_3021_; 
v_es_3016_ = lean_ctor_get(v_x_3013_, 0);
v___x_3017_ = lean_box(2);
v___x_3018_ = ((size_t)31ULL);
v___x_3019_ = lean_usize_land(v_x_3014_, v___x_3018_);
v_j_3020_ = lean_usize_to_nat(v___x_3019_);
v___x_3021_ = lean_array_get_borrowed(v___x_3017_, v_es_3016_, v_j_3020_);
lean_dec(v_j_3020_);
switch(lean_obj_tag(v___x_3021_))
{
case 0:
{
lean_object* v_key_3022_; lean_object* v_val_3023_; uint8_t v___y_3025_; lean_object* v_expr_3028_; uint64_t v_configKey_3029_; lean_object* v_expr_3030_; uint64_t v_configKey_3031_; uint8_t v___x_3032_; 
v_key_3022_ = lean_ctor_get(v___x_3021_, 0);
v_val_3023_ = lean_ctor_get(v___x_3021_, 1);
v_expr_3028_ = lean_ctor_get(v_x_3015_, 0);
v_configKey_3029_ = lean_ctor_get_uint64(v_x_3015_, sizeof(void*)*1);
v_expr_3030_ = lean_ctor_get(v_key_3022_, 0);
v_configKey_3031_ = lean_ctor_get_uint64(v_key_3022_, sizeof(void*)*1);
v___x_3032_ = lean_expr_equal(v_expr_3028_, v_expr_3030_);
if (v___x_3032_ == 0)
{
v___y_3025_ = v___x_3032_;
goto v___jp_3024_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_uint64_dec_eq(v_configKey_3029_, v_configKey_3031_);
v___y_3025_ = v___x_3033_;
goto v___jp_3024_;
}
v___jp_3024_:
{
if (v___y_3025_ == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_box(0);
return v___x_3026_;
}
else
{
lean_object* v___x_3027_; 
lean_inc(v_val_3023_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_val_3023_);
return v___x_3027_;
}
}
}
case 1:
{
lean_object* v_node_3034_; size_t v___x_3035_; size_t v___x_3036_; 
v_node_3034_ = lean_ctor_get(v___x_3021_, 0);
v___x_3035_ = ((size_t)5ULL);
v___x_3036_ = lean_usize_shift_right(v_x_3014_, v___x_3035_);
v_x_3013_ = v_node_3034_;
v_x_3014_ = v___x_3036_;
goto _start;
}
default: 
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_box(0);
return v___x_3038_;
}
}
}
else
{
lean_object* v_ks_3039_; lean_object* v_vs_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_ks_3039_ = lean_ctor_get(v_x_3013_, 0);
v_vs_3040_ = lean_ctor_get(v_x_3013_, 1);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3039_, v_vs_3040_, v___x_3041_, v_x_3015_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
size_t v_x_2990__boxed_3046_; lean_object* v_res_3047_; 
v_x_2990__boxed_3046_ = lean_unbox_usize(v_x_3044_);
lean_dec(v_x_3044_);
v_res_3047_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3043_, v_x_2990__boxed_3046_, v_x_3045_);
lean_dec_ref(v_x_3045_);
lean_dec_ref(v_x_3043_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v_expr_3050_; uint64_t v_configKey_3051_; uint64_t v___x_3052_; uint64_t v___x_3053_; size_t v___x_3054_; lean_object* v___x_3055_; 
v_expr_3050_ = lean_ctor_get(v_x_3049_, 0);
v_configKey_3051_ = lean_ctor_get_uint64(v_x_3049_, sizeof(void*)*1);
v___x_3052_ = l_Lean_Expr_hash(v_expr_3050_);
v___x_3053_ = lean_uint64_mix_hash(v___x_3052_, v_configKey_3051_);
v___x_3054_ = lean_uint64_to_usize(v___x_3053_);
v___x_3055_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3048_, v___x_3054_, v_x_3049_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3056_, lean_object* v_x_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3056_, v_x_3057_);
lean_dec_ref(v_x_3057_);
lean_dec_ref(v_x_3056_);
return v_res_3058_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
switch(lean_obj_tag(v_e_3062_))
{
case 0:
{
lean_object* v_deBruijnIndex_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_deBruijnIndex_3100_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_deBruijnIndex_3100_);
lean_dec_ref_known(v_e_3062_, 1);
v___x_3101_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3102_ = l_Lean_mkBVar(v_deBruijnIndex_3100_);
v___x_3103_ = l_Lean_MessageData_ofExpr(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3104_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3105_;
}
case 1:
{
lean_object* v_fvarId_3106_; lean_object* v___x_3107_; 
v_fvarId_3106_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_fvarId_3106_);
lean_dec_ref_known(v_e_3062_, 1);
v___x_3107_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3106_, v_a_3063_, v_a_3065_, v_a_3066_);
return v___x_3107_;
}
case 2:
{
lean_object* v_mvarId_3108_; lean_object* v___x_3109_; 
v_mvarId_3108_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_mvarId_3108_);
lean_dec_ref_known(v_e_3062_, 1);
v___x_3109_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3108_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3109_;
}
case 3:
{
lean_object* v_u_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_u_3110_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_u_3110_);
lean_dec_ref_known(v_e_3062_, 1);
v___x_3111_ = l_Lean_Level_succ___override(v_u_3110_);
v___x_3112_ = l_Lean_mkSort(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
case 4:
{
lean_object* v_declName_3114_; lean_object* v_us_3115_; 
v_declName_3114_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_declName_3114_);
v_us_3115_ = lean_ctor_get(v_e_3062_, 1);
lean_inc(v_us_3115_);
if (lean_obj_tag(v_us_3115_) == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref_known(v_e_3062_, 2);
v___x_3132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3132_;
}
else
{
uint8_t v_cacheInferType_3133_; 
v_cacheInferType_3133_ = lean_ctor_get_uint8(v_a_3063_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3133_ == 0)
{
lean_dec_ref_known(v_e_3062_, 2);
goto v___jp_3116_;
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = l_Lean_Expr_hasMVar(v_e_3062_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3201_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3201_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3201_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3180_; lean_object* v_cache_3181_; lean_object* v_inferType_3182_; lean_object* v___x_3183_; 
v___x_3180_ = lean_st_ref_get(v_a_3064_);
v_cache_3181_ = lean_ctor_get(v___x_3180_, 1);
lean_inc_ref(v_cache_3181_);
lean_dec(v___x_3180_);
v_inferType_3182_ = lean_ctor_get(v_cache_3181_, 0);
lean_inc_ref(v_inferType_3182_);
lean_dec_ref(v_cache_3181_);
v___x_3183_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3182_, v_a_3136_);
lean_dec_ref(v_inferType_3182_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_toCold_3184_; lean_object* v_cancelTk_x3f_3185_; 
lean_del_object(v___x_3138_);
v_toCold_3184_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3185_ = lean_ctor_get(v_toCold_3184_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3185_) == 1)
{
lean_object* v_val_3186_; uint8_t v___x_3187_; 
v_val_3186_ = lean_ctor_get(v_cancelTk_x3f_3185_, 0);
v___x_3187_ = l_IO_CancelToken_isSet(v_val_3186_);
if (v___x_3187_ == 0)
{
goto v___jp_3140_;
}
else
{
lean_object* v___x_3188_; lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3136_);
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v___x_3188_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
goto v___jp_3140_;
}
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3199_; 
lean_dec(v_a_3136_);
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v_val_3197_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v___x_3183_, 1);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v_val_3197_);
v___x_3199_ = v___x_3138_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_val_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
v___jp_3140_:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; uint8_t v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
v___x_3143_ = l_Lean_Expr_hasMVar(v_a_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3178_; 
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3179_);
v___x_3145_ = v___x_3141_;
v_isShared_3146_ = v_isSharedCheck_3178_;
goto v_resetjp_3144_;
}
else
{
lean_dec(v___x_3141_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3178_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v_cache_3148_; lean_object* v_mctx_3149_; lean_object* v_zetaDeltaFVarIds_3150_; lean_object* v_postponed_3151_; lean_object* v_diag_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3177_; 
v___x_3147_ = lean_st_ref_take(v_a_3064_);
v_cache_3148_ = lean_ctor_get(v___x_3147_, 1);
v_mctx_3149_ = lean_ctor_get(v___x_3147_, 0);
v_zetaDeltaFVarIds_3150_ = lean_ctor_get(v___x_3147_, 2);
v_postponed_3151_ = lean_ctor_get(v___x_3147_, 3);
v_diag_3152_ = lean_ctor_get(v___x_3147_, 4);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3154_ = v___x_3147_;
v_isShared_3155_ = v_isSharedCheck_3177_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_diag_3152_);
lean_inc(v_postponed_3151_);
lean_inc(v_zetaDeltaFVarIds_3150_);
lean_inc(v_cache_3148_);
lean_inc(v_mctx_3149_);
lean_dec(v___x_3147_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3177_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v_inferType_3156_; lean_object* v_funInfo_3157_; lean_object* v_synthInstance_3158_; lean_object* v_whnf_3159_; lean_object* v_defEqTrans_3160_; lean_object* v_defEqPerm_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3176_; 
v_inferType_3156_ = lean_ctor_get(v_cache_3148_, 0);
v_funInfo_3157_ = lean_ctor_get(v_cache_3148_, 1);
v_synthInstance_3158_ = lean_ctor_get(v_cache_3148_, 2);
v_whnf_3159_ = lean_ctor_get(v_cache_3148_, 3);
v_defEqTrans_3160_ = lean_ctor_get(v_cache_3148_, 4);
v_defEqPerm_3161_ = lean_ctor_get(v_cache_3148_, 5);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_cache_3148_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3163_ = v_cache_3148_;
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_defEqPerm_3161_);
lean_inc(v_defEqTrans_3160_);
lean_inc(v_whnf_3159_);
lean_inc(v_synthInstance_3158_);
lean_inc(v_funInfo_3157_);
lean_inc(v_inferType_3156_);
lean_dec(v_cache_3148_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3176_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
lean_inc(v_a_3142_);
v___x_3165_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3156_, v_a_3136_, v_a_3142_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_funInfo_3157_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_synthInstance_3158_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_whnf_3159_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_defEqTrans_3160_);
lean_ctor_set(v_reuseFailAlloc_3175_, 5, v_defEqPerm_3161_);
v___x_3167_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v___x_3167_);
v___x_3169_ = v___x_3154_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_mctx_3149_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_zetaDeltaFVarIds_3150_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_postponed_3151_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_diag_3152_);
v___x_3169_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_st_ref_put(v_a_3064_, v___x_3169_);
if (v_isShared_3146_ == 0)
{
v___x_3172_ = v___x_3145_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3142_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3142_);
lean_dec(v_a_3136_);
return v___x_3141_;
}
}
else
{
lean_dec(v_a_3136_);
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v_a_3202_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3135_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3135_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3062_, 2);
goto v___jp_3116_;
}
}
}
v___jp_3116_:
{
lean_object* v_toCold_3117_; lean_object* v_cancelTk_x3f_3118_; 
v_toCold_3117_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3118_ = lean_ctor_get(v_toCold_3117_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3118_) == 1)
{
lean_object* v_val_3119_; uint8_t v___x_3120_; 
v_val_3119_ = lean_ctor_get(v_cancelTk_x3f_3118_, 0);
v___x_3120_ = l_IO_CancelToken_isSet(v_val_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v___x_3122_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3131_;
}
}
}
case 5:
{
lean_object* v_fn_3210_; uint8_t v_cacheInferType_3211_; lean_object* v_nargs_3212_; lean_object* v___x_3213_; lean_object* v_dummy_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_fn_3210_ = lean_ctor_get(v_e_3062_, 0);
v_cacheInferType_3211_ = lean_ctor_get_uint8(v_a_3063_, sizeof(void*)*7 + 3);
v_nargs_3212_ = l_Lean_Expr_getAppNumArgs(v_e_3062_);
v___x_3213_ = l_Lean_Expr_getAppFn(v_fn_3210_);
v_dummy_3214_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3212_);
v___x_3215_ = lean_mk_array(v_nargs_3212_, v_dummy_3214_);
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = lean_nat_sub(v_nargs_3212_, v___x_3216_);
lean_dec(v_nargs_3212_);
lean_inc_ref(v_e_3062_);
v___x_3218_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3062_, v___x_3215_, v___x_3217_);
if (v_cacheInferType_3211_ == 0)
{
lean_dec_ref_known(v_e_3062_, 2);
goto v___jp_3219_;
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Lean_Expr_hasMVar(v_e_3062_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3302_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3302_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3302_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3281_; lean_object* v_cache_3282_; lean_object* v_inferType_3283_; lean_object* v___x_3284_; 
v___x_3281_ = lean_st_ref_get(v_a_3064_);
v_cache_3282_ = lean_ctor_get(v___x_3281_, 1);
lean_inc_ref(v_cache_3282_);
lean_dec(v___x_3281_);
v_inferType_3283_ = lean_ctor_get(v_cache_3282_, 0);
lean_inc_ref(v_inferType_3283_);
lean_dec_ref(v_cache_3282_);
v___x_3284_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3283_, v_a_3237_);
lean_dec_ref(v_inferType_3283_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_toCold_3285_; lean_object* v_cancelTk_x3f_3286_; 
lean_del_object(v___x_3239_);
v_toCold_3285_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3286_ = lean_ctor_get(v_toCold_3285_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3286_) == 1)
{
lean_object* v_val_3287_; uint8_t v___x_3288_; 
v_val_3287_ = lean_ctor_get(v_cancelTk_x3f_3286_, 0);
v___x_3288_ = l_IO_CancelToken_isSet(v_val_3287_);
if (v___x_3288_ == 0)
{
goto v___jp_3241_;
}
else
{
lean_object* v___x_3289_; lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3237_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3213_);
v___x_3289_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
goto v___jp_3241_;
}
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3300_; 
lean_dec(v_a_3237_);
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3213_);
v_val_3298_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_val_3298_);
lean_dec_ref_known(v___x_3284_, 1);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v_val_3298_);
v___x_3300_ = v___x_3239_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
v___jp_3241_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3213_, v___x_3218_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v___x_3218_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; uint8_t v___x_3244_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
v___x_3244_ = l_Lean_Expr_hasMVar(v_a_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3242_, 0);
lean_dec(v_unused_3280_);
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3279_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3279_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v_cache_3249_; lean_object* v_mctx_3250_; lean_object* v_zetaDeltaFVarIds_3251_; lean_object* v_postponed_3252_; lean_object* v_diag_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3278_; 
v___x_3248_ = lean_st_ref_take(v_a_3064_);
v_cache_3249_ = lean_ctor_get(v___x_3248_, 1);
v_mctx_3250_ = lean_ctor_get(v___x_3248_, 0);
v_zetaDeltaFVarIds_3251_ = lean_ctor_get(v___x_3248_, 2);
v_postponed_3252_ = lean_ctor_get(v___x_3248_, 3);
v_diag_3253_ = lean_ctor_get(v___x_3248_, 4);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3255_ = v___x_3248_;
v_isShared_3256_ = v_isSharedCheck_3278_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_diag_3253_);
lean_inc(v_postponed_3252_);
lean_inc(v_zetaDeltaFVarIds_3251_);
lean_inc(v_cache_3249_);
lean_inc(v_mctx_3250_);
lean_dec(v___x_3248_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3278_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v_inferType_3257_; lean_object* v_funInfo_3258_; lean_object* v_synthInstance_3259_; lean_object* v_whnf_3260_; lean_object* v_defEqTrans_3261_; lean_object* v_defEqPerm_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3277_; 
v_inferType_3257_ = lean_ctor_get(v_cache_3249_, 0);
v_funInfo_3258_ = lean_ctor_get(v_cache_3249_, 1);
v_synthInstance_3259_ = lean_ctor_get(v_cache_3249_, 2);
v_whnf_3260_ = lean_ctor_get(v_cache_3249_, 3);
v_defEqTrans_3261_ = lean_ctor_get(v_cache_3249_, 4);
v_defEqPerm_3262_ = lean_ctor_get(v_cache_3249_, 5);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_cache_3249_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3264_ = v_cache_3249_;
v_isShared_3265_ = v_isSharedCheck_3277_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_defEqPerm_3262_);
lean_inc(v_defEqTrans_3261_);
lean_inc(v_whnf_3260_);
lean_inc(v_synthInstance_3259_);
lean_inc(v_funInfo_3258_);
lean_inc(v_inferType_3257_);
lean_dec(v_cache_3249_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3277_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_inc(v_a_3243_);
v___x_3266_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3257_, v_a_3237_, v_a_3243_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_funInfo_3258_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_synthInstance_3259_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_whnf_3260_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_defEqTrans_3261_);
lean_ctor_set(v_reuseFailAlloc_3276_, 5, v_defEqPerm_3262_);
v___x_3268_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3270_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 1, v___x_3268_);
v___x_3270_ = v___x_3255_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_mctx_3250_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_zetaDeltaFVarIds_3251_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_postponed_3252_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v_diag_3253_);
v___x_3270_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = lean_st_ref_put(v_a_3064_, v___x_3270_);
if (v_isShared_3247_ == 0)
{
v___x_3273_ = v___x_3246_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3243_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3243_);
lean_dec(v_a_3237_);
return v___x_3242_;
}
}
else
{
lean_dec(v_a_3237_);
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3213_);
v_a_3303_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3236_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3236_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3062_, 2);
goto v___jp_3219_;
}
}
v___jp_3219_:
{
lean_object* v_toCold_3220_; lean_object* v_cancelTk_x3f_3221_; 
v_toCold_3220_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3221_ = lean_ctor_get(v_toCold_3220_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3221_) == 1)
{
lean_object* v_val_3222_; uint8_t v___x_3223_; 
v_val_3222_ = lean_ctor_get(v_cancelTk_x3f_3221_, 0);
v___x_3223_ = l_IO_CancelToken_isSet(v_val_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3213_, v___x_3218_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v___x_3218_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___x_3213_);
v___x_3225_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3213_, v___x_3218_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v___x_3218_);
return v___x_3234_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3311_; 
v_cacheInferType_3311_ = lean_ctor_get_uint8(v_a_3063_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3311_ == 0)
{
goto v___jp_3084_;
}
else
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Lean_Expr_hasMVar(v_e_3062_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_inc_ref(v_e_3062_);
v___x_3313_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3379_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3379_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3379_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3358_; lean_object* v_cache_3359_; lean_object* v_inferType_3360_; lean_object* v___x_3361_; 
v___x_3358_ = lean_st_ref_get(v_a_3064_);
v_cache_3359_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_cache_3359_);
lean_dec(v___x_3358_);
v_inferType_3360_ = lean_ctor_get(v_cache_3359_, 0);
lean_inc_ref(v_inferType_3360_);
lean_dec_ref(v_cache_3359_);
v___x_3361_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3360_, v_a_3314_);
lean_dec_ref(v_inferType_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_toCold_3362_; lean_object* v_cancelTk_x3f_3363_; 
lean_del_object(v___x_3316_);
v_toCold_3362_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3363_ = lean_ctor_get(v_toCold_3362_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3363_) == 1)
{
lean_object* v_val_3364_; uint8_t v___x_3365_; 
v_val_3364_ = lean_ctor_get(v_cancelTk_x3f_3363_, 0);
v___x_3365_ = l_IO_CancelToken_isSet(v_val_3364_);
if (v___x_3365_ == 0)
{
goto v___jp_3318_;
}
else
{
lean_object* v___x_3366_; lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v_a_3314_);
lean_dec_ref_known(v_e_3062_, 3);
v___x_3366_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
goto v___jp_3318_;
}
}
else
{
lean_object* v_val_3375_; lean_object* v___x_3377_; 
lean_dec(v_a_3314_);
lean_dec_ref_known(v_e_3062_, 3);
v_val_3375_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3361_, 1);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_val_3375_);
v___x_3377_ = v___x_3316_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_val_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
v___jp_3318_:
{
lean_object* v___x_3319_; 
v___x_3319_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; uint8_t v___x_3321_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
v___x_3321_ = l_Lean_Expr_hasMVar(v_a_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3356_; 
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3357_);
v___x_3323_ = v___x_3319_;
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
else
{
lean_dec(v___x_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3356_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v_cache_3326_; lean_object* v_mctx_3327_; lean_object* v_zetaDeltaFVarIds_3328_; lean_object* v_postponed_3329_; lean_object* v_diag_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3355_; 
v___x_3325_ = lean_st_ref_take(v_a_3064_);
v_cache_3326_ = lean_ctor_get(v___x_3325_, 1);
v_mctx_3327_ = lean_ctor_get(v___x_3325_, 0);
v_zetaDeltaFVarIds_3328_ = lean_ctor_get(v___x_3325_, 2);
v_postponed_3329_ = lean_ctor_get(v___x_3325_, 3);
v_diag_3330_ = lean_ctor_get(v___x_3325_, 4);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3332_ = v___x_3325_;
v_isShared_3333_ = v_isSharedCheck_3355_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_diag_3330_);
lean_inc(v_postponed_3329_);
lean_inc(v_zetaDeltaFVarIds_3328_);
lean_inc(v_cache_3326_);
lean_inc(v_mctx_3327_);
lean_dec(v___x_3325_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3355_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_inferType_3334_; lean_object* v_funInfo_3335_; lean_object* v_synthInstance_3336_; lean_object* v_whnf_3337_; lean_object* v_defEqTrans_3338_; lean_object* v_defEqPerm_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3354_; 
v_inferType_3334_ = lean_ctor_get(v_cache_3326_, 0);
v_funInfo_3335_ = lean_ctor_get(v_cache_3326_, 1);
v_synthInstance_3336_ = lean_ctor_get(v_cache_3326_, 2);
v_whnf_3337_ = lean_ctor_get(v_cache_3326_, 3);
v_defEqTrans_3338_ = lean_ctor_get(v_cache_3326_, 4);
v_defEqPerm_3339_ = lean_ctor_get(v_cache_3326_, 5);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_cache_3326_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3341_ = v_cache_3326_;
v_isShared_3342_ = v_isSharedCheck_3354_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_defEqPerm_3339_);
lean_inc(v_defEqTrans_3338_);
lean_inc(v_whnf_3337_);
lean_inc(v_synthInstance_3336_);
lean_inc(v_funInfo_3335_);
lean_inc(v_inferType_3334_);
lean_dec(v_cache_3326_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3354_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_inc(v_a_3320_);
v___x_3343_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3334_, v_a_3314_, v_a_3320_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_funInfo_3335_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_synthInstance_3336_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v_whnf_3337_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_defEqTrans_3338_);
lean_ctor_set(v_reuseFailAlloc_3353_, 5, v_defEqPerm_3339_);
v___x_3345_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v___x_3345_);
v___x_3347_ = v___x_3332_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_mctx_3327_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_zetaDeltaFVarIds_3328_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_postponed_3329_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v_diag_3330_);
v___x_3347_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_st_ref_put(v_a_3064_, v___x_3347_);
if (v_isShared_3324_ == 0)
{
v___x_3350_ = v___x_3323_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3320_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3320_);
lean_dec(v_a_3314_);
return v___x_3319_;
}
}
else
{
lean_dec(v_a_3314_);
return v___x_3319_;
}
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref_known(v_e_3062_, 3);
v_a_3380_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3313_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3313_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
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
lean_object* v_a_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_a_3388_ = lean_ctor_get(v_e_3062_, 0);
lean_inc_ref(v_a_3388_);
lean_dec_ref_known(v_e_3062_, 1);
v___x_3389_ = l_Lean_Literal_type(v_a_3388_);
lean_dec_ref(v_a_3388_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
case 10:
{
lean_object* v_expr_3391_; 
v_expr_3391_ = lean_ctor_get(v_e_3062_, 1);
lean_inc_ref(v_expr_3391_);
lean_dec_ref_known(v_e_3062_, 2);
v_e_3062_ = v_expr_3391_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3393_; lean_object* v_idx_3394_; lean_object* v_struct_3395_; uint8_t v_cacheInferType_3412_; 
v_typeName_3393_ = lean_ctor_get(v_e_3062_, 0);
lean_inc(v_typeName_3393_);
v_idx_3394_ = lean_ctor_get(v_e_3062_, 1);
lean_inc(v_idx_3394_);
v_struct_3395_ = lean_ctor_get(v_e_3062_, 2);
lean_inc_ref(v_struct_3395_);
v_cacheInferType_3412_ = lean_ctor_get_uint8(v_a_3063_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3412_ == 0)
{
lean_dec_ref_known(v_e_3062_, 3);
goto v___jp_3396_;
}
else
{
uint8_t v___x_3413_; 
v___x_3413_ = l_Lean_Expr_hasMVar(v_e_3062_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3480_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3480_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3480_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3459_; lean_object* v_cache_3460_; lean_object* v_inferType_3461_; lean_object* v___x_3462_; 
v___x_3459_ = lean_st_ref_get(v_a_3064_);
v_cache_3460_ = lean_ctor_get(v___x_3459_, 1);
lean_inc_ref(v_cache_3460_);
lean_dec(v___x_3459_);
v_inferType_3461_ = lean_ctor_get(v_cache_3460_, 0);
lean_inc_ref(v_inferType_3461_);
lean_dec_ref(v_cache_3460_);
v___x_3462_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3461_, v_a_3415_);
lean_dec_ref(v_inferType_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_toCold_3463_; lean_object* v_cancelTk_x3f_3464_; 
lean_del_object(v___x_3417_);
v_toCold_3463_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3464_ = lean_ctor_get(v_toCold_3463_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3464_) == 1)
{
lean_object* v_val_3465_; uint8_t v___x_3466_; 
v_val_3465_ = lean_ctor_get(v_cancelTk_x3f_3464_, 0);
v___x_3466_ = l_IO_CancelToken_isSet(v_val_3465_);
if (v___x_3466_ == 0)
{
goto v___jp_3419_;
}
else
{
lean_object* v___x_3467_; lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec(v_a_3415_);
lean_dec_ref(v_struct_3395_);
lean_dec(v_idx_3394_);
lean_dec(v_typeName_3393_);
v___x_3467_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
goto v___jp_3419_;
}
}
else
{
lean_object* v_val_3476_; lean_object* v___x_3478_; 
lean_dec(v_a_3415_);
lean_dec_ref(v_struct_3395_);
lean_dec(v_idx_3394_);
lean_dec(v_typeName_3393_);
v_val_3476_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3462_, 1);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v_val_3476_);
v___x_3478_ = v___x_3417_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_val_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
v___jp_3419_:
{
lean_object* v___x_3420_; 
v___x_3420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3393_, v_idx_3394_, v_struct_3395_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; uint8_t v___x_3422_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
v___x_3422_ = l_Lean_Expr_hasMVar(v_a_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3457_; 
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v___x_3420_, 0);
lean_dec(v_unused_3458_);
v___x_3424_ = v___x_3420_;
v_isShared_3425_ = v_isSharedCheck_3457_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___x_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3457_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v_cache_3427_; lean_object* v_mctx_3428_; lean_object* v_zetaDeltaFVarIds_3429_; lean_object* v_postponed_3430_; lean_object* v_diag_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3456_; 
v___x_3426_ = lean_st_ref_take(v_a_3064_);
v_cache_3427_ = lean_ctor_get(v___x_3426_, 1);
v_mctx_3428_ = lean_ctor_get(v___x_3426_, 0);
v_zetaDeltaFVarIds_3429_ = lean_ctor_get(v___x_3426_, 2);
v_postponed_3430_ = lean_ctor_get(v___x_3426_, 3);
v_diag_3431_ = lean_ctor_get(v___x_3426_, 4);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3433_ = v___x_3426_;
v_isShared_3434_ = v_isSharedCheck_3456_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_diag_3431_);
lean_inc(v_postponed_3430_);
lean_inc(v_zetaDeltaFVarIds_3429_);
lean_inc(v_cache_3427_);
lean_inc(v_mctx_3428_);
lean_dec(v___x_3426_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3456_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_inferType_3435_; lean_object* v_funInfo_3436_; lean_object* v_synthInstance_3437_; lean_object* v_whnf_3438_; lean_object* v_defEqTrans_3439_; lean_object* v_defEqPerm_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3455_; 
v_inferType_3435_ = lean_ctor_get(v_cache_3427_, 0);
v_funInfo_3436_ = lean_ctor_get(v_cache_3427_, 1);
v_synthInstance_3437_ = lean_ctor_get(v_cache_3427_, 2);
v_whnf_3438_ = lean_ctor_get(v_cache_3427_, 3);
v_defEqTrans_3439_ = lean_ctor_get(v_cache_3427_, 4);
v_defEqPerm_3440_ = lean_ctor_get(v_cache_3427_, 5);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_cache_3427_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3442_ = v_cache_3427_;
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_defEqPerm_3440_);
lean_inc(v_defEqTrans_3439_);
lean_inc(v_whnf_3438_);
lean_inc(v_synthInstance_3437_);
lean_inc(v_funInfo_3436_);
lean_inc(v_inferType_3435_);
lean_dec(v_cache_3427_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_inc(v_a_3421_);
v___x_3444_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3435_, v_a_3415_, v_a_3421_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_funInfo_3436_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_synthInstance_3437_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_whnf_3438_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_defEqTrans_3439_);
lean_ctor_set(v_reuseFailAlloc_3454_, 5, v_defEqPerm_3440_);
v___x_3446_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3446_);
v___x_3448_ = v___x_3433_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_mctx_3428_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_zetaDeltaFVarIds_3429_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_postponed_3430_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_diag_3431_);
v___x_3448_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_st_ref_put(v_a_3064_, v___x_3448_);
if (v_isShared_3425_ == 0)
{
v___x_3451_ = v___x_3424_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3421_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3421_);
lean_dec(v_a_3415_);
return v___x_3420_;
}
}
else
{
lean_dec(v_a_3415_);
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v_struct_3395_);
lean_dec(v_idx_3394_);
lean_dec(v_typeName_3393_);
v_a_3481_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3414_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3414_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3062_, 3);
goto v___jp_3396_;
}
}
v___jp_3396_:
{
lean_object* v_toCold_3397_; lean_object* v_cancelTk_x3f_3398_; 
v_toCold_3397_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3398_ = lean_ctor_get(v_toCold_3397_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3398_) == 1)
{
lean_object* v_val_3399_; uint8_t v___x_3400_; 
v_val_3399_ = lean_ctor_get(v_cancelTk_x3f_3398_, 0);
v___x_3400_ = l_IO_CancelToken_isSet(v_val_3399_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3393_, v_idx_3394_, v_struct_3395_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v_struct_3395_);
lean_dec(v_idx_3394_);
lean_dec(v_typeName_3393_);
v___x_3402_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v___x_3411_; 
v___x_3411_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3393_, v_idx_3394_, v_struct_3395_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3411_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3489_; 
v_cacheInferType_3489_ = lean_ctor_get_uint8(v_a_3063_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3489_ == 0)
{
goto v___jp_3068_;
}
else
{
uint8_t v___x_3490_; 
v___x_3490_ = l_Lean_Expr_hasMVar(v_e_3062_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
lean_inc_ref(v_e_3062_);
v___x_3491_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3557_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3557_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3557_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3536_; lean_object* v_cache_3537_; lean_object* v_inferType_3538_; lean_object* v___x_3539_; 
v___x_3536_ = lean_st_ref_get(v_a_3064_);
v_cache_3537_ = lean_ctor_get(v___x_3536_, 1);
lean_inc_ref(v_cache_3537_);
lean_dec(v___x_3536_);
v_inferType_3538_ = lean_ctor_get(v_cache_3537_, 0);
lean_inc_ref(v_inferType_3538_);
lean_dec_ref(v_cache_3537_);
v___x_3539_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3538_, v_a_3492_);
lean_dec_ref(v_inferType_3538_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_toCold_3540_; lean_object* v_cancelTk_x3f_3541_; 
lean_del_object(v___x_3494_);
v_toCold_3540_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3541_ = lean_ctor_get(v_toCold_3540_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3541_) == 1)
{
lean_object* v_val_3542_; uint8_t v___x_3543_; 
v_val_3542_ = lean_ctor_get(v_cancelTk_x3f_3541_, 0);
v___x_3543_ = l_IO_CancelToken_isSet(v_val_3542_);
if (v___x_3543_ == 0)
{
goto v___jp_3496_;
}
else
{
lean_object* v___x_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_a_3492_);
lean_dec_ref(v_e_3062_);
v___x_3544_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
goto v___jp_3496_;
}
}
else
{
lean_object* v_val_3553_; lean_object* v___x_3555_; 
lean_dec(v_a_3492_);
lean_dec_ref(v_e_3062_);
v_val_3553_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_val_3553_);
lean_dec_ref_known(v___x_3539_, 1);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_val_3553_);
v___x_3555_ = v___x_3494_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_val_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
v___jp_3496_:
{
lean_object* v___x_3497_; 
v___x_3497_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; uint8_t v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
v___x_3499_ = l_Lean_Expr_hasMVar(v_a_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3534_; 
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v___x_3497_, 0);
lean_dec(v_unused_3535_);
v___x_3501_ = v___x_3497_;
v_isShared_3502_ = v_isSharedCheck_3534_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v___x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3534_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v_cache_3504_; lean_object* v_mctx_3505_; lean_object* v_zetaDeltaFVarIds_3506_; lean_object* v_postponed_3507_; lean_object* v_diag_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3533_; 
v___x_3503_ = lean_st_ref_take(v_a_3064_);
v_cache_3504_ = lean_ctor_get(v___x_3503_, 1);
v_mctx_3505_ = lean_ctor_get(v___x_3503_, 0);
v_zetaDeltaFVarIds_3506_ = lean_ctor_get(v___x_3503_, 2);
v_postponed_3507_ = lean_ctor_get(v___x_3503_, 3);
v_diag_3508_ = lean_ctor_get(v___x_3503_, 4);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3510_ = v___x_3503_;
v_isShared_3511_ = v_isSharedCheck_3533_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_diag_3508_);
lean_inc(v_postponed_3507_);
lean_inc(v_zetaDeltaFVarIds_3506_);
lean_inc(v_cache_3504_);
lean_inc(v_mctx_3505_);
lean_dec(v___x_3503_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3533_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_inferType_3512_; lean_object* v_funInfo_3513_; lean_object* v_synthInstance_3514_; lean_object* v_whnf_3515_; lean_object* v_defEqTrans_3516_; lean_object* v_defEqPerm_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3532_; 
v_inferType_3512_ = lean_ctor_get(v_cache_3504_, 0);
v_funInfo_3513_ = lean_ctor_get(v_cache_3504_, 1);
v_synthInstance_3514_ = lean_ctor_get(v_cache_3504_, 2);
v_whnf_3515_ = lean_ctor_get(v_cache_3504_, 3);
v_defEqTrans_3516_ = lean_ctor_get(v_cache_3504_, 4);
v_defEqPerm_3517_ = lean_ctor_get(v_cache_3504_, 5);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_cache_3504_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3519_ = v_cache_3504_;
v_isShared_3520_ = v_isSharedCheck_3532_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_defEqPerm_3517_);
lean_inc(v_defEqTrans_3516_);
lean_inc(v_whnf_3515_);
lean_inc(v_synthInstance_3514_);
lean_inc(v_funInfo_3513_);
lean_inc(v_inferType_3512_);
lean_dec(v_cache_3504_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3532_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
lean_inc(v_a_3498_);
v___x_3521_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3512_, v_a_3492_, v_a_3498_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3521_);
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_funInfo_3513_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_synthInstance_3514_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_whnf_3515_);
lean_ctor_set(v_reuseFailAlloc_3531_, 4, v_defEqTrans_3516_);
lean_ctor_set(v_reuseFailAlloc_3531_, 5, v_defEqPerm_3517_);
v___x_3523_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3523_);
v___x_3525_ = v___x_3510_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_mctx_3505_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_zetaDeltaFVarIds_3506_);
lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_postponed_3507_);
lean_ctor_set(v_reuseFailAlloc_3530_, 4, v_diag_3508_);
v___x_3525_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_st_ref_put(v_a_3064_, v___x_3525_);
if (v_isShared_3502_ == 0)
{
v___x_3528_ = v___x_3501_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3498_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3498_);
lean_dec(v_a_3492_);
return v___x_3497_;
}
}
else
{
lean_dec(v_a_3492_);
return v___x_3497_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v_e_3062_);
v_a_3558_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3491_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3491_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
goto v___jp_3068_;
}
}
}
}
v___jp_3068_:
{
lean_object* v_toCold_3069_; lean_object* v_cancelTk_x3f_3070_; 
v_toCold_3069_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3070_ = lean_ctor_get(v_toCold_3069_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3070_) == 1)
{
lean_object* v_val_3071_; uint8_t v___x_3072_; 
v_val_3071_ = lean_ctor_get(v_cancelTk_x3f_3070_, 0);
v___x_3072_ = l_IO_CancelToken_isSet(v_val_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_e_3062_);
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
v___x_3083_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3083_;
}
}
v___jp_3084_:
{
lean_object* v_toCold_3085_; lean_object* v_cancelTk_x3f_3086_; 
v_toCold_3085_ = lean_ctor_get(v_a_3065_, 0);
v_cancelTk_x3f_3086_ = lean_ctor_get(v_toCold_3085_, 3);
if (lean_obj_tag(v_cancelTk_x3f_3086_) == 1)
{
lean_object* v_val_3087_; uint8_t v___x_3088_; 
v_val_3087_ = lean_ctor_get(v_cancelTk_x3f_3086_, 0);
v___x_3088_ = l_IO_CancelToken_isSet(v_val_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref(v_e_3062_);
v___x_3090_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3574_, v_x_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3579_, v_x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3582_, v_x_3583_, v_x_3584_);
lean_dec_ref(v_x_3584_);
lean_dec_ref(v_x_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3586_, lean_object* v_x_3587_, size_t v_x_3588_, size_t v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3587_, v_x_3588_, v_x_3589_, v_x_3590_, v_x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
size_t v_x_4028__boxed_3599_; size_t v_x_4029__boxed_3600_; lean_object* v_res_3601_; 
v_x_4028__boxed_3599_ = lean_unbox_usize(v_x_3595_);
lean_dec(v_x_3595_);
v_x_4029__boxed_3600_ = lean_unbox_usize(v_x_3596_);
lean_dec(v_x_3596_);
v_res_3601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3593_, v_x_3594_, v_x_4028__boxed_3599_, v_x_4029__boxed_3600_, v_x_3597_, v_x_3598_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3602_, lean_object* v_x_3603_, size_t v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3603_, v_x_3604_, v_x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
size_t v_x_4045__boxed_3611_; lean_object* v_res_3612_; 
v_x_4045__boxed_3611_ = lean_unbox_usize(v_x_3609_);
lean_dec(v_x_3609_);
v_res_3612_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3607_, v_x_3608_, v_x_4045__boxed_3611_, v_x_3610_);
lean_dec_ref(v_x_3610_);
lean_dec_ref(v_x_3608_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3613_, lean_object* v_n_3614_, lean_object* v_k_3615_, lean_object* v_v_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3614_, v_k_3615_, v_v_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3618_, size_t v_depth_3619_, lean_object* v_keys_3620_, lean_object* v_vals_3621_, lean_object* v_heq_3622_, lean_object* v_i_3623_, lean_object* v_entries_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3619_, v_keys_3620_, v_vals_3621_, v_i_3623_, v_entries_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3626_, lean_object* v_depth_3627_, lean_object* v_keys_3628_, lean_object* v_vals_3629_, lean_object* v_heq_3630_, lean_object* v_i_3631_, lean_object* v_entries_3632_){
_start:
{
size_t v_depth_boxed_3633_; lean_object* v_res_3634_; 
v_depth_boxed_3633_ = lean_unbox_usize(v_depth_3627_);
lean_dec(v_depth_3627_);
v_res_3634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3626_, v_depth_boxed_3633_, v_keys_3628_, v_vals_3629_, v_heq_3630_, v_i_3631_, v_entries_3632_);
lean_dec_ref(v_vals_3629_);
lean_dec_ref(v_keys_3628_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3635_, lean_object* v_keys_3636_, lean_object* v_vals_3637_, lean_object* v_heq_3638_, lean_object* v_i_3639_, lean_object* v_k_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3636_, v_vals_3637_, v_i_3639_, v_k_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3642_, lean_object* v_keys_3643_, lean_object* v_vals_3644_, lean_object* v_heq_3645_, lean_object* v_i_3646_, lean_object* v_k_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3642_, v_keys_3643_, v_vals_3644_, v_heq_3645_, v_i_3646_, v_k_3647_);
lean_dec_ref(v_k_3647_);
lean_dec_ref(v_vals_3644_);
lean_dec_ref(v_keys_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_, lean_object* v_x_3652_, lean_object* v_x_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3650_, v_x_3651_, v_x_3652_, v_x_3653_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = l_Lean_maxRecDepthErrorMessage;
v___x_3661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3663_ = l_Lean_MessageData_ofFormat(v___x_3662_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3665_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3666_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v___x_3664_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3667_){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_ref_3667_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3675_, lean_object* v_ref_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3676_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_ref_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3683_, v_ref_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3743_; uint8_t v_beta_3744_; 
v___x_3743_ = l_Lean_Meta_Context_config(v___y_3692_);
v_beta_3744_ = lean_ctor_get_uint8(v___x_3743_, 13);
if (v_beta_3744_ == 0)
{
lean_dec_ref(v___x_3743_);
goto v___jp_3697_;
}
else
{
uint8_t v_iota_3745_; 
v_iota_3745_ = lean_ctor_get_uint8(v___x_3743_, 12);
if (v_iota_3745_ == 0)
{
lean_dec_ref(v___x_3743_);
goto v___jp_3697_;
}
else
{
uint8_t v_zeta_3746_; 
v_zeta_3746_ = lean_ctor_get_uint8(v___x_3743_, 15);
if (v_zeta_3746_ == 0)
{
lean_dec_ref(v___x_3743_);
goto v___jp_3697_;
}
else
{
uint8_t v_zetaHave_3747_; 
v_zetaHave_3747_ = lean_ctor_get_uint8(v___x_3743_, 18);
if (v_zetaHave_3747_ == 0)
{
lean_dec_ref(v___x_3743_);
goto v___jp_3697_;
}
else
{
uint8_t v_zetaDelta_3748_; 
v_zetaDelta_3748_ = lean_ctor_get_uint8(v___x_3743_, 16);
if (v_zetaDelta_3748_ == 0)
{
lean_dec_ref(v___x_3743_);
goto v___jp_3697_;
}
else
{
uint8_t v_etaStruct_3749_; uint8_t v_proj_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v_etaStruct_3749_ = lean_ctor_get_uint8(v___x_3743_, 10);
v_proj_3750_ = lean_ctor_get_uint8(v___x_3743_, 14);
lean_dec_ref(v___x_3743_);
v___x_3751_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_3750_);
v___x_3752_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_3753_ = lean_nat_dec_eq(v___x_3751_, v___x_3752_);
lean_dec(v___x_3751_);
if (v___x_3753_ == 0)
{
goto v___jp_3697_;
}
else
{
uint8_t v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = 0;
v___x_3755_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3749_, v___x_3754_);
if (v___x_3755_ == 0)
{
goto v___jp_3697_;
}
else
{
lean_object* v___x_3756_; 
v___x_3756_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec_ref(v___y_3692_);
return v___x_3756_;
}
}
}
}
}
}
}
v___jp_3697_:
{
lean_object* v___x_3698_; uint8_t v_foApprox_3699_; uint8_t v_ctxApprox_3700_; uint8_t v_quasiPatternApprox_3701_; uint8_t v_constApprox_3702_; uint8_t v_isDefEqStuckEx_3703_; uint8_t v_unificationHints_3704_; uint8_t v_proofIrrelevance_3705_; uint8_t v_assignSyntheticOpaque_3706_; uint8_t v_offsetCnstrs_3707_; uint8_t v_transparency_3708_; uint8_t v_univApprox_3709_; uint8_t v_zetaUnused_3710_; uint8_t v_canUnfoldPredicateConfig_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3742_; 
v___x_3698_ = l_Lean_Meta_Context_config(v___y_3692_);
v_foApprox_3699_ = lean_ctor_get_uint8(v___x_3698_, 0);
v_ctxApprox_3700_ = lean_ctor_get_uint8(v___x_3698_, 1);
v_quasiPatternApprox_3701_ = lean_ctor_get_uint8(v___x_3698_, 2);
v_constApprox_3702_ = lean_ctor_get_uint8(v___x_3698_, 3);
v_isDefEqStuckEx_3703_ = lean_ctor_get_uint8(v___x_3698_, 4);
v_unificationHints_3704_ = lean_ctor_get_uint8(v___x_3698_, 5);
v_proofIrrelevance_3705_ = lean_ctor_get_uint8(v___x_3698_, 6);
v_assignSyntheticOpaque_3706_ = lean_ctor_get_uint8(v___x_3698_, 7);
v_offsetCnstrs_3707_ = lean_ctor_get_uint8(v___x_3698_, 8);
v_transparency_3708_ = lean_ctor_get_uint8(v___x_3698_, 9);
v_univApprox_3709_ = lean_ctor_get_uint8(v___x_3698_, 11);
v_zetaUnused_3710_ = lean_ctor_get_uint8(v___x_3698_, 17);
v_canUnfoldPredicateConfig_3711_ = lean_ctor_get_uint8(v___x_3698_, 19);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3713_ = v___x_3698_;
v_isShared_3714_ = v_isSharedCheck_3742_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v___x_3698_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3742_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
uint8_t v___x_3715_; uint8_t v___x_3716_; uint8_t v___x_3717_; lean_object* v___x_3719_; 
v___x_3715_ = 1;
v___x_3716_ = 0;
v___x_3717_ = 2;
if (v_isShared_3714_ == 0)
{
v___x_3719_ = v___x_3713_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 0, v_foApprox_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 1, v_ctxApprox_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 2, v_quasiPatternApprox_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 3, v_constApprox_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 4, v_isDefEqStuckEx_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 5, v_unificationHints_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 6, v_proofIrrelevance_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 7, v_assignSyntheticOpaque_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 8, v_offsetCnstrs_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 9, v_transparency_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 11, v_univApprox_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 17, v_zetaUnused_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3741_, 19, v_canUnfoldPredicateConfig_3711_);
v___x_3719_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
uint8_t v_trackZetaDelta_3720_; lean_object* v_zetaDeltaSet_3721_; lean_object* v_lctx_3722_; lean_object* v_localInstances_3723_; lean_object* v_defEqCtx_x3f_3724_; lean_object* v_synthPendingDepth_3725_; lean_object* v_customCanUnfoldPredicate_x3f_3726_; uint8_t v_univApprox_3727_; uint8_t v_inTypeClassResolution_3728_; uint8_t v_cacheInferType_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3739_; 
lean_ctor_set_uint8(v___x_3719_, 10, v___x_3716_);
lean_ctor_set_uint8(v___x_3719_, 12, v___x_3715_);
lean_ctor_set_uint8(v___x_3719_, 13, v___x_3715_);
lean_ctor_set_uint8(v___x_3719_, 14, v___x_3717_);
lean_ctor_set_uint8(v___x_3719_, 15, v___x_3715_);
lean_ctor_set_uint8(v___x_3719_, 16, v___x_3715_);
lean_ctor_set_uint8(v___x_3719_, 18, v___x_3715_);
v_trackZetaDelta_3720_ = lean_ctor_get_uint8(v___y_3692_, sizeof(void*)*7);
v_zetaDeltaSet_3721_ = lean_ctor_get(v___y_3692_, 1);
v_lctx_3722_ = lean_ctor_get(v___y_3692_, 2);
v_localInstances_3723_ = lean_ctor_get(v___y_3692_, 3);
v_defEqCtx_x3f_3724_ = lean_ctor_get(v___y_3692_, 4);
v_synthPendingDepth_3725_ = lean_ctor_get(v___y_3692_, 5);
v_customCanUnfoldPredicate_x3f_3726_ = lean_ctor_get(v___y_3692_, 6);
v_univApprox_3727_ = lean_ctor_get_uint8(v___y_3692_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3728_ = lean_ctor_get_uint8(v___y_3692_, sizeof(void*)*7 + 2);
v_cacheInferType_3729_ = lean_ctor_get_uint8(v___y_3692_, sizeof(void*)*7 + 3);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___y_3692_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; 
v_unused_3740_ = lean_ctor_get(v___y_3692_, 0);
lean_dec(v_unused_3740_);
v___x_3731_ = v___y_3692_;
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3726_);
lean_inc(v_synthPendingDepth_3725_);
lean_inc(v_defEqCtx_x3f_3724_);
lean_inc(v_localInstances_3723_);
lean_inc(v_lctx_3722_);
lean_inc(v_zetaDeltaSet_3721_);
lean_dec(v___y_3692_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3739_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
uint64_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
v___x_3733_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3719_);
v___x_3734_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3734_, 0, v___x_3719_);
lean_ctor_set_uint64(v___x_3734_, sizeof(void*)*1, v___x_3733_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v___x_3734_);
v___x_3736_ = v___x_3731_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_zetaDeltaSet_3721_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_lctx_3722_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_localInstances_3723_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v_defEqCtx_x3f_3724_);
lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_synthPendingDepth_3725_);
lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_customCanUnfoldPredicate_x3f_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7, v_trackZetaDelta_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 1, v_univApprox_3727_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3728_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 3, v_cacheInferType_3729_);
v___x_3736_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3691_, v___x_3736_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec_ref(v___x_3736_);
return v___x_3737_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v___y_3771_; lean_object* v_toCold_3788_; lean_object* v_options_3789_; lean_object* v_currRecDepth_3790_; lean_object* v_maxRecDepth_3791_; lean_object* v_ref_3792_; lean_object* v_currNamespace_3793_; lean_object* v_openDecls_3794_; lean_object* v_initHeartbeats_3795_; lean_object* v_maxHeartbeats_3796_; lean_object* v_currMacroScope_3797_; uint8_t v_diag_3798_; uint8_t v_suppressElabErrors_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3838_; 
v_toCold_3788_ = lean_ctor_get(v_a_3767_, 0);
v_options_3789_ = lean_ctor_get(v_a_3767_, 1);
v_currRecDepth_3790_ = lean_ctor_get(v_a_3767_, 2);
v_maxRecDepth_3791_ = lean_ctor_get(v_a_3767_, 3);
v_ref_3792_ = lean_ctor_get(v_a_3767_, 4);
v_currNamespace_3793_ = lean_ctor_get(v_a_3767_, 5);
v_openDecls_3794_ = lean_ctor_get(v_a_3767_, 6);
v_initHeartbeats_3795_ = lean_ctor_get(v_a_3767_, 7);
v_maxHeartbeats_3796_ = lean_ctor_get(v_a_3767_, 8);
v_currMacroScope_3797_ = lean_ctor_get(v_a_3767_, 9);
v_diag_3798_ = lean_ctor_get_uint8(v_a_3767_, sizeof(void*)*10);
v_suppressElabErrors_3799_ = lean_ctor_get_uint8(v_a_3767_, sizeof(void*)*10 + 1);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3801_ = v_a_3767_;
v_isShared_3802_ = v_isSharedCheck_3838_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_currMacroScope_3797_);
lean_inc(v_maxHeartbeats_3796_);
lean_inc(v_initHeartbeats_3795_);
lean_inc(v_openDecls_3794_);
lean_inc(v_currNamespace_3793_);
lean_inc(v_ref_3792_);
lean_inc(v_maxRecDepth_3791_);
lean_inc(v_currRecDepth_3790_);
lean_inc(v_options_3789_);
lean_inc(v_toCold_3788_);
lean_dec(v_a_3767_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3838_;
goto v_resetjp_3800_;
}
v___jp_3770_:
{
if (lean_obj_tag(v___y_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_a_3772_ = lean_ctor_get(v___y_3771_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___y_3771_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___y_3771_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___y_3771_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v_a_3780_ = lean_ctor_get(v___y_3771_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___y_3771_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___y_3771_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___y_3771_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
v_resetjp_3800_:
{
lean_object* v___x_3834_; uint8_t v___x_3835_; 
v___x_3834_ = lean_unsigned_to_nat(0u);
v___x_3835_ = lean_nat_dec_eq(v_maxRecDepth_3791_, v___x_3834_);
if (v___x_3835_ == 0)
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_nat_dec_eq(v_currRecDepth_3790_, v_maxRecDepth_3791_);
if (v___x_3836_ == 0)
{
goto v___jp_3803_;
}
else
{
lean_object* v___x_3837_; 
lean_del_object(v___x_3801_);
lean_dec(v_currMacroScope_3797_);
lean_dec(v_maxHeartbeats_3796_);
lean_dec(v_initHeartbeats_3795_);
lean_dec(v_openDecls_3794_);
lean_dec(v_currNamespace_3793_);
lean_dec(v_maxRecDepth_3791_);
lean_dec(v_currRecDepth_3790_);
lean_dec_ref(v_options_3789_);
lean_dec_ref(v_toCold_3788_);
lean_dec(v_a_3768_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec_ref(v_e_3764_);
v___x_3837_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3792_);
return v___x_3837_;
}
}
else
{
goto v___jp_3803_;
}
v___jp_3803_:
{
lean_object* v___x_3804_; uint8_t v_transparency_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3804_ = l_Lean_Meta_Context_config(v_a_3765_);
v_transparency_3805_ = lean_ctor_get_uint8(v___x_3804_, 9);
lean_dec_ref(v___x_3804_);
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_add(v_currRecDepth_3790_, v___x_3806_);
lean_dec(v_currRecDepth_3790_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 2, v___x_3807_);
v___x_3809_ = v___x_3801_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_toCold_3788_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_options_3789_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_maxRecDepth_3791_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v_ref_3792_);
lean_ctor_set(v_reuseFailAlloc_3833_, 5, v_currNamespace_3793_);
lean_ctor_set(v_reuseFailAlloc_3833_, 6, v_openDecls_3794_);
lean_ctor_set(v_reuseFailAlloc_3833_, 7, v_initHeartbeats_3795_);
lean_ctor_set(v_reuseFailAlloc_3833_, 8, v_maxHeartbeats_3796_);
lean_ctor_set(v_reuseFailAlloc_3833_, 9, v_currMacroScope_3797_);
lean_ctor_set_uint8(v_reuseFailAlloc_3833_, sizeof(void*)*10, v_diag_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3833_, sizeof(void*)*10 + 1, v_suppressElabErrors_3799_);
v___x_3809_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
uint8_t v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = 1;
v___x_3811_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3805_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3764_, v_a_3765_, v_a_3766_, v___x_3809_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v___x_3809_);
lean_dec(v_a_3766_);
v___y_3771_ = v___x_3812_;
goto v___jp_3770_;
}
else
{
lean_object* v_keyedConfig_3813_; uint8_t v_trackZetaDelta_3814_; lean_object* v_zetaDeltaSet_3815_; lean_object* v_lctx_3816_; lean_object* v_localInstances_3817_; lean_object* v_defEqCtx_x3f_3818_; lean_object* v_synthPendingDepth_3819_; lean_object* v_customCanUnfoldPredicate_x3f_3820_; uint8_t v_univApprox_3821_; uint8_t v_inTypeClassResolution_3822_; uint8_t v_cacheInferType_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3832_; 
v_keyedConfig_3813_ = lean_ctor_get(v_a_3765_, 0);
v_trackZetaDelta_3814_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7);
v_zetaDeltaSet_3815_ = lean_ctor_get(v_a_3765_, 1);
v_lctx_3816_ = lean_ctor_get(v_a_3765_, 2);
v_localInstances_3817_ = lean_ctor_get(v_a_3765_, 3);
v_defEqCtx_x3f_3818_ = lean_ctor_get(v_a_3765_, 4);
v_synthPendingDepth_3819_ = lean_ctor_get(v_a_3765_, 5);
v_customCanUnfoldPredicate_x3f_3820_ = lean_ctor_get(v_a_3765_, 6);
v_univApprox_3821_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3822_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 2);
v_cacheInferType_3823_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 3);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3825_ = v_a_3765_;
v_isShared_3826_ = v_isSharedCheck_3832_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3820_);
lean_inc(v_synthPendingDepth_3819_);
lean_inc(v_defEqCtx_x3f_3818_);
lean_inc(v_localInstances_3817_);
lean_inc(v_lctx_3816_);
lean_inc(v_zetaDeltaSet_3815_);
lean_inc(v_keyedConfig_3813_);
lean_dec(v_a_3765_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3832_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3810_, v_keyedConfig_3813_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_zetaDeltaSet_3815_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_lctx_3816_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_localInstances_3817_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_defEqCtx_x3f_3818_);
lean_ctor_set(v_reuseFailAlloc_3831_, 5, v_synthPendingDepth_3819_);
lean_ctor_set(v_reuseFailAlloc_3831_, 6, v_customCanUnfoldPredicate_x3f_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*7, v_trackZetaDelta_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*7 + 1, v_univApprox_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, sizeof(void*)*7 + 3, v_cacheInferType_3823_);
v___x_3829_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3764_, v___x_3829_, v_a_3766_, v___x_3809_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v___x_3809_);
lean_dec(v_a_3766_);
v___y_3771_ = v___x_3830_;
goto v___jp_3770_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = lean_infer_type(v_e_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3846_){
_start:
{
switch(lean_obj_tag(v_x_3846_))
{
case 0:
{
uint8_t v___x_3847_; 
v___x_3847_ = 1;
return v___x_3847_;
}
case 2:
{
lean_object* v_a_3848_; lean_object* v_a_3849_; uint8_t v___x_3850_; 
v_a_3848_ = lean_ctor_get(v_x_3846_, 0);
v_a_3849_ = lean_ctor_get(v_x_3846_, 1);
v___x_3850_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3848_);
if (v___x_3850_ == 0)
{
return v___x_3850_;
}
else
{
v_x_3846_ = v_a_3849_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_ctor_get(v_x_3846_, 1);
v_x_3846_ = v_a_3852_;
goto _start;
}
default: 
{
uint8_t v___x_3854_; 
v___x_3854_ = 0;
return v___x_3854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3855_){
_start:
{
uint8_t v_res_3856_; lean_object* v_r_3857_; 
v_res_3856_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3855_);
lean_dec(v_x_3855_);
v_r_3857_ = lean_box(v_res_3856_);
return v_r_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; lean_object* v_mctx_3862_; lean_object* v___x_3863_; lean_object* v_fst_3864_; lean_object* v_snd_3865_; lean_object* v___x_3866_; lean_object* v_cache_3867_; lean_object* v_zetaDeltaFVarIds_3868_; lean_object* v_postponed_3869_; lean_object* v_diag_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3879_; 
v___x_3861_ = lean_st_ref_get(v___y_3859_);
v_mctx_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc_ref(v_mctx_3862_);
lean_dec(v___x_3861_);
v___x_3863_ = lean_instantiate_level_mvars(v_mctx_3862_, v_l_3858_);
v_fst_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_fst_3864_);
v_snd_3865_ = lean_ctor_get(v___x_3863_, 1);
lean_inc(v_snd_3865_);
lean_dec_ref(v___x_3863_);
v___x_3866_ = lean_st_ref_take(v___y_3859_);
v_cache_3867_ = lean_ctor_get(v___x_3866_, 1);
v_zetaDeltaFVarIds_3868_ = lean_ctor_get(v___x_3866_, 2);
v_postponed_3869_ = lean_ctor_get(v___x_3866_, 3);
v_diag_3870_ = lean_ctor_get(v___x_3866_, 4);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; 
v_unused_3880_ = lean_ctor_get(v___x_3866_, 0);
lean_dec(v_unused_3880_);
v___x_3872_ = v___x_3866_;
v_isShared_3873_ = v_isSharedCheck_3879_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_diag_3870_);
lean_inc(v_postponed_3869_);
lean_inc(v_zetaDeltaFVarIds_3868_);
lean_inc(v_cache_3867_);
lean_dec(v___x_3866_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3879_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v_fst_3864_);
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_fst_3864_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_cache_3867_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_zetaDeltaFVarIds_3868_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_postponed_3869_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v_diag_3870_);
v___x_3875_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_st_ref_put(v___y_3859_, v___x_3875_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v_snd_3865_);
return v___x_3877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3881_, v___y_3882_);
lean_dec(v___y_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3885_, v___y_3887_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
switch(lean_obj_tag(v_x_3899_))
{
case 3:
{
lean_object* v_u_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v_u_3910_ = lean_ctor_get(v_x_3899_, 0);
lean_inc(v_u_3910_);
lean_dec_ref_known(v_x_3899_, 1);
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = lean_nat_dec_eq(v_x_3900_, v___x_3911_);
lean_dec(v_x_3900_);
if (v___x_3912_ == 0)
{
lean_dec(v_u_3910_);
goto v___jp_3906_;
}
else
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3910_, v_a_3902_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3918_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3914_);
lean_dec(v_a_3914_);
v___x_3919_ = l_Lean_Bool_toLBool(v___x_3918_);
v___x_3920_ = lean_box(v___x_3919_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3920_);
v___x_3922_ = v___x_3916_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
v_a_3925_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3913_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3913_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3933_; lean_object* v_zero_3934_; uint8_t v_isZero_3935_; 
v_body_3933_ = lean_ctor_get(v_x_3899_, 2);
lean_inc_ref(v_body_3933_);
lean_dec_ref_known(v_x_3899_, 3);
v_zero_3934_ = lean_unsigned_to_nat(0u);
v_isZero_3935_ = lean_nat_dec_eq(v_x_3900_, v_zero_3934_);
if (v_isZero_3935_ == 1)
{
uint8_t v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec_ref(v_body_3933_);
lean_dec(v_x_3900_);
v___x_3936_ = 0;
v___x_3937_ = lean_box(v___x_3936_);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
return v___x_3938_;
}
else
{
lean_object* v_one_3939_; lean_object* v_n_3940_; 
v_one_3939_ = lean_unsigned_to_nat(1u);
v_n_3940_ = lean_nat_sub(v_x_3900_, v_one_3939_);
lean_dec(v_x_3900_);
v_x_3899_ = v_body_3933_;
v_x_3900_ = v_n_3940_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3942_; 
v_body_3942_ = lean_ctor_get(v_x_3899_, 3);
lean_inc_ref(v_body_3942_);
lean_dec_ref_known(v_x_3899_, 4);
v_x_3899_ = v_body_3942_;
goto _start;
}
case 10:
{
lean_object* v_expr_3944_; 
v_expr_3944_ = lean_ctor_get(v_x_3899_, 1);
lean_inc_ref(v_expr_3944_);
lean_dec_ref_known(v_x_3899_, 2);
v_x_3899_ = v_expr_3944_;
goto _start;
}
default: 
{
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3899_);
goto v___jp_3906_;
}
}
v___jp_3906_:
{
uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = 2;
v___x_3908_ = lean_box(v___x_3907_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3946_, lean_object* v_x_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3946_, v_x_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3954_, lean_object* v_x_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
switch(lean_obj_tag(v_x_3954_))
{
case 4:
{
lean_object* v_declName_3961_; lean_object* v_us_3962_; lean_object* v___x_3963_; 
v_declName_3961_ = lean_ctor_get(v_x_3954_, 0);
lean_inc(v_declName_3961_);
v_us_3962_ = lean_ctor_get(v_x_3954_, 1);
lean_inc(v_us_3962_);
lean_dec_ref_known(v_x_3954_, 2);
v___x_3963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3961_, v_us_3962_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3964_, v_x_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_3965_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_x_3955_);
v_a_3966_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3963_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3963_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3974_; lean_object* v___x_3975_; 
v_fvarId_3974_ = lean_ctor_get(v_x_3954_, 0);
lean_inc(v_fvarId_3974_);
lean_dec_ref_known(v_x_3954_, 1);
v___x_3975_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3974_, v_a_3956_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3977_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3976_, v_x_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_3977_;
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_x_3955_);
v_a_3978_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3975_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3975_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3986_; lean_object* v___x_3987_; 
v_mvarId_3986_ = lean_ctor_get(v_x_3954_, 0);
lean_inc(v_mvarId_3986_);
lean_dec_ref_known(v_x_3954_, 1);
v___x_3987_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3986_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3989_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3988_, v_x_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
return v___x_3989_;
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_x_3955_);
v_a_3990_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3987_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3987_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
case 5:
{
lean_object* v_fn_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_fn_3998_ = lean_ctor_get(v_x_3954_, 0);
lean_inc_ref(v_fn_3998_);
lean_dec_ref_known(v_x_3954_, 2);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_nat_add(v_x_3955_, v___x_3999_);
lean_dec(v_x_3955_);
v_x_3954_ = v_fn_3998_;
v_x_3955_ = v___x_4000_;
goto _start;
}
case 10:
{
lean_object* v_expr_4002_; 
v_expr_4002_ = lean_ctor_get(v_x_3954_, 1);
lean_inc_ref(v_expr_4002_);
lean_dec_ref_known(v_x_3954_, 2);
v_x_3954_ = v_expr_4002_;
goto _start;
}
case 8:
{
lean_object* v_body_4004_; 
v_body_4004_ = lean_ctor_get(v_x_3954_, 3);
lean_inc_ref(v_body_4004_);
lean_dec_ref_known(v_x_3954_, 4);
v_x_3954_ = v_body_4004_;
goto _start;
}
case 6:
{
lean_object* v_body_4006_; lean_object* v_zero_4007_; uint8_t v_isZero_4008_; 
v_body_4006_ = lean_ctor_get(v_x_3954_, 2);
lean_inc_ref(v_body_4006_);
lean_dec_ref_known(v_x_3954_, 3);
v_zero_4007_ = lean_unsigned_to_nat(0u);
v_isZero_4008_ = lean_nat_dec_eq(v_x_3955_, v_zero_4007_);
if (v_isZero_4008_ == 1)
{
uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec_ref(v_body_4006_);
lean_dec(v_x_3955_);
v___x_4009_ = 0;
v___x_4010_ = lean_box(v___x_4009_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
else
{
lean_object* v_one_4012_; lean_object* v_n_4013_; 
v_one_4012_ = lean_unsigned_to_nat(1u);
v_n_4013_ = lean_nat_sub(v_x_3955_, v_one_4012_);
lean_dec(v_x_3955_);
v_x_3954_ = v_body_4006_;
v_x_3955_ = v_n_4013_;
goto _start;
}
}
default: 
{
uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_dec(v_x_3955_);
lean_dec_ref(v_x_3954_);
v___x_4015_ = 2;
v___x_4016_ = lean_box(v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4018_, lean_object* v_x_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4018_, v_x_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
switch(lean_obj_tag(v_x_4026_))
{
case 0:
{
uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec_ref_known(v_x_4026_, 1);
v___x_4032_ = 2;
v___x_4033_ = lean_box(v___x_4032_);
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
case 1:
{
lean_object* v_fvarId_4035_; lean_object* v___x_4036_; 
v_fvarId_4035_ = lean_ctor_get(v_x_4026_, 0);
lean_inc(v_fvarId_4035_);
lean_dec_ref_known(v_x_4026_, 1);
v___x_4036_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4035_, v_a_4027_, v_a_4029_, v_a_4030_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = lean_unsigned_to_nat(0u);
v___x_4039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4037_, v___x_4038_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4036_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4036_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4048_; lean_object* v___x_4049_; 
v_mvarId_4048_ = lean_ctor_get(v_x_4026_, 0);
lean_inc(v_mvarId_4048_);
lean_dec_ref_known(v_x_4026_, 1);
v___x_4049_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4048_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4050_, v___x_4051_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4052_;
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
v_a_4053_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4049_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4049_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
case 4:
{
lean_object* v_declName_4061_; lean_object* v_us_4062_; lean_object* v___x_4063_; 
v_declName_4061_ = lean_ctor_get(v_x_4026_, 0);
lean_inc(v_declName_4061_);
v_us_4062_ = lean_ctor_get(v_x_4026_, 1);
lean_inc(v_us_4062_);
lean_dec_ref_known(v_x_4026_, 2);
v___x_4063_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4061_, v_us_4062_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_unsigned_to_nat(0u);
v___x_4066_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4064_, v___x_4065_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4066_;
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_a_4067_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4063_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4063_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
case 5:
{
lean_object* v_fn_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_fn_4075_ = lean_ctor_get(v_x_4026_, 0);
lean_inc_ref(v_fn_4075_);
lean_dec_ref_known(v_x_4026_, 2);
v___x_4076_ = lean_unsigned_to_nat(1u);
v___x_4077_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4075_, v___x_4076_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4077_;
}
case 7:
{
lean_object* v_body_4078_; 
v_body_4078_ = lean_ctor_get(v_x_4026_, 2);
lean_inc_ref(v_body_4078_);
lean_dec_ref_known(v_x_4026_, 3);
v_x_4026_ = v_body_4078_;
goto _start;
}
case 8:
{
lean_object* v_body_4080_; 
v_body_4080_ = lean_ctor_get(v_x_4026_, 3);
lean_inc_ref(v_body_4080_);
lean_dec_ref_known(v_x_4026_, 4);
v_x_4026_ = v_body_4080_;
goto _start;
}
case 10:
{
lean_object* v_expr_4082_; 
v_expr_4082_ = lean_ctor_get(v_x_4026_, 1);
lean_inc_ref(v_expr_4082_);
lean_dec_ref_known(v_x_4026_, 2);
v_x_4026_ = v_expr_4082_;
goto _start;
}
case 11:
{
uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_dec_ref_known(v_x_4026_, 3);
v___x_4084_ = 2;
v___x_4085_ = lean_box(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
default: 
{
uint8_t v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
lean_dec_ref(v_x_4026_);
v___x_4087_ = 0;
v___x_4088_ = lean_box(v___x_4087_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_isPropQuick(v_x_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v___x_4103_; 
lean_inc_ref(v_e_4097_);
v___x_4103_ = l_Lean_Meta_isPropQuick(v_e_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4160_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4160_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4160_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_unbox(v_a_4104_);
lean_dec(v_a_4104_);
switch(v___x_4108_)
{
case 0:
{
uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
lean_dec_ref(v_e_4097_);
v___x_4109_ = 0;
v___x_4110_ = lean_box(v___x_4109_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4110_);
v___x_4112_ = v___x_4106_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
case 1:
{
uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
lean_dec_ref(v_e_4097_);
v___x_4114_ = 1;
v___x_4115_ = lean_box(v___x_4114_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4115_);
v___x_4117_ = v___x_4106_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
default: 
{
lean_object* v___x_4119_; 
lean_del_object(v___x_4106_);
lean_inc(v_a_4101_);
lean_inc_ref(v_a_4100_);
lean_inc(v_a_4099_);
lean_inc_ref(v_a_4098_);
v___x_4119_ = lean_infer_type(v_e_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = l_Lean_Meta_whnfD(v_a_4120_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4143_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4124_ = v___x_4121_;
v_isShared_4125_ = v_isSharedCheck_4143_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4121_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4143_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
if (lean_obj_tag(v_a_4122_) == 3)
{
lean_object* v_u_4126_; lean_object* v___x_4127_; lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4137_; 
lean_del_object(v___x_4124_);
v_u_4126_ = lean_ctor_get(v_a_4122_, 0);
lean_inc(v_u_4126_);
lean_dec_ref_known(v_a_4122_, 1);
v___x_4127_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4126_, v_a_4099_);
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4128_);
lean_dec(v_a_4128_);
v___x_4133_ = lean_box(v___x_4132_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4133_);
v___x_4135_ = v___x_4130_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
else
{
uint8_t v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
lean_dec(v_a_4122_);
v___x_4138_ = 0;
v___x_4139_ = lean_box(v___x_4138_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4139_);
v___x_4141_ = v___x_4124_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_a_4144_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4121_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4121_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_a_4152_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4119_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4119_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v_e_4097_);
v_a_4161_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4103_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4103_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Meta_isProp(v_e_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4176_){
_start:
{
switch(lean_obj_tag(v_x_4176_))
{
case 0:
{
lean_object* v___x_4177_; 
v___x_4177_ = lean_unsigned_to_nat(0u);
return v___x_4177_;
}
case 1:
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
return v___x_4178_;
}
case 2:
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_unsigned_to_nat(2u);
return v___x_4179_;
}
default: 
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_unsigned_to_nat(3u);
return v___x_4180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4181_);
lean_dec(v_x_4181_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4183_, lean_object* v_k_4184_){
_start:
{
if (lean_obj_tag(v_t_4183_) == 3)
{
lean_object* v_idx_4185_; lean_object* v___x_4186_; 
v_idx_4185_ = lean_ctor_get(v_t_4183_, 0);
lean_inc(v_idx_4185_);
lean_dec_ref_known(v_t_4183_, 1);
v___x_4186_ = lean_apply_1(v_k_4184_, v_idx_4185_);
return v___x_4186_;
}
else
{
lean_dec(v_t_4183_);
return v_k_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4187_, lean_object* v_ctorIdx_4188_, lean_object* v_t_4189_, lean_object* v_h_4190_, lean_object* v_k_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4189_, v_k_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4193_, lean_object* v_ctorIdx_4194_, lean_object* v_t_4195_, lean_object* v_h_4196_, lean_object* v_k_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4193_, v_ctorIdx_4194_, v_t_4195_, v_h_4196_, v_k_4197_);
lean_dec(v_ctorIdx_4194_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4199_, lean_object* v_false_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4199_, v_false_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4202_, lean_object* v_t_4203_, lean_object* v_h_4204_, lean_object* v_false_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4203_, v_false_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4207_, lean_object* v_true_4208_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4207_, v_true_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4210_, lean_object* v_t_4211_, lean_object* v_h_4212_, lean_object* v_true_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4211_, v_true_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4215_, lean_object* v_undef_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4215_, v_undef_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4218_, lean_object* v_t_4219_, lean_object* v_h_4220_, lean_object* v_undef_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4219_, v_undef_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4223_, lean_object* v_bvar_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4223_, v_bvar_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4226_, lean_object* v_t_4227_, lean_object* v_h_4228_, lean_object* v_bvar_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4227_, v_bvar_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4231_){
_start:
{
switch(v_x_4231_)
{
case 0:
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_box(0);
return v___x_4232_;
}
case 1:
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_box(1);
return v___x_4233_;
}
default: 
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_box(2);
return v___x_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4235_){
_start:
{
uint8_t v_x_25__boxed_4236_; lean_object* v_res_4237_; 
v_x_25__boxed_4236_ = lean_unbox(v_x_4235_);
v_res_4237_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4236_);
return v_res_4237_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4238_){
_start:
{
switch(lean_obj_tag(v_x_4238_))
{
case 0:
{
uint8_t v___x_4239_; 
v___x_4239_ = 0;
return v___x_4239_;
}
case 1:
{
uint8_t v___x_4240_; 
v___x_4240_ = 1;
return v___x_4240_;
}
default: 
{
uint8_t v___x_4241_; 
v___x_4241_ = 2;
return v___x_4241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4242_){
_start:
{
uint8_t v_res_4243_; lean_object* v_r_4244_; 
v_res_4243_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4242_);
lean_dec(v_x_4242_);
v_r_4244_ = lean_box(v_res_4243_);
return v_r_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4246_){
_start:
{
switch(lean_obj_tag(v_e_4246_))
{
case 3:
{
lean_object* v_u_4247_; uint8_t v___x_4248_; 
v_u_4247_ = lean_ctor_get(v_e_4246_, 0);
v___x_4248_ = l_Lean_Level_isNeverZero(v_u_4247_);
if (v___x_4248_ == 0)
{
uint8_t v___x_4249_; 
v___x_4249_ = l_Lean_Level_isZero(v_u_4247_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_box(2);
return v___x_4250_;
}
else
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_box(1);
return v___x_4251_;
}
}
else
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_box(0);
return v___x_4252_;
}
}
case 5:
{
lean_object* v_fn_4253_; 
v_fn_4253_ = lean_ctor_get(v_e_4246_, 0);
if (lean_obj_tag(v_fn_4253_) == 4)
{
lean_object* v_declName_4254_; 
v_declName_4254_ = lean_ctor_get(v_fn_4253_, 0);
if (lean_obj_tag(v_declName_4254_) == 1)
{
lean_object* v_pre_4255_; 
v_pre_4255_ = lean_ctor_get(v_declName_4254_, 0);
if (lean_obj_tag(v_pre_4255_) == 0)
{
lean_object* v_arg_4256_; lean_object* v_str_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v_arg_4256_ = lean_ctor_get(v_e_4246_, 1);
v_str_4257_ = lean_ctor_get(v_declName_4254_, 1);
v___x_4258_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4259_ = lean_string_dec_eq(v_str_4257_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_box(2);
return v___x_4260_;
}
else
{
v_e_4246_ = v_arg_4256_;
goto _start;
}
}
else
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_box(2);
return v___x_4262_;
}
}
else
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_box(2);
return v___x_4263_;
}
}
else
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_box(2);
return v___x_4264_;
}
}
default: 
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_box(2);
return v___x_4265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4266_);
lean_dec_ref(v_e_4266_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4268_, lean_object* v_binderType_4269_){
_start:
{
if (lean_obj_tag(v_r_4268_) == 3)
{
lean_object* v_idx_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4282_; 
v_idx_4270_ = lean_ctor_get(v_r_4268_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_r_4268_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4272_ = v_r_4268_;
v_isShared_4273_ = v_isSharedCheck_4282_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_idx_4270_);
lean_dec(v_r_4268_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4282_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v_zero_4274_; uint8_t v_isZero_4275_; 
v_zero_4274_ = lean_unsigned_to_nat(0u);
v_isZero_4275_ = lean_nat_dec_eq(v_idx_4270_, v_zero_4274_);
if (v_isZero_4275_ == 1)
{
lean_object* v___x_4276_; 
lean_del_object(v___x_4272_);
lean_dec(v_idx_4270_);
v___x_4276_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4269_);
return v___x_4276_;
}
else
{
lean_object* v_one_4277_; lean_object* v_n_4278_; lean_object* v___x_4280_; 
v_one_4277_ = lean_unsigned_to_nat(1u);
v_n_4278_ = lean_nat_sub(v_idx_4270_, v_one_4277_);
lean_dec(v_idx_4270_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v_n_4278_);
v___x_4280_ = v___x_4272_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_n_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
return v_r_4268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4283_, lean_object* v_binderType_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4283_, v_binderType_4284_);
lean_dec_ref(v_binderType_4284_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4286_, lean_object* v_x_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_type_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; 
switch(lean_obj_tag(v_x_4286_))
{
case 7:
{
lean_object* v_binderType_4321_; lean_object* v_body_4322_; lean_object* v_zero_4323_; uint8_t v_isZero_4324_; 
v_binderType_4321_ = lean_ctor_get(v_x_4286_, 1);
v_body_4322_ = lean_ctor_get(v_x_4286_, 2);
v_zero_4323_ = lean_unsigned_to_nat(0u);
v_isZero_4324_ = lean_nat_dec_eq(v_x_4287_, v_zero_4323_);
if (v_isZero_4324_ == 1)
{
v_type_4294_ = v_x_4286_;
v___y_4295_ = v_a_4288_;
v___y_4296_ = v_a_4289_;
v___y_4297_ = v_a_4290_;
v___y_4298_ = v_a_4291_;
goto v___jp_4293_;
}
else
{
lean_object* v_one_4325_; lean_object* v_n_4326_; lean_object* v___x_4327_; 
lean_inc_ref(v_body_4322_);
lean_inc_ref(v_binderType_4321_);
lean_dec_ref_known(v_x_4286_, 3);
v_one_4325_ = lean_unsigned_to_nat(1u);
v_n_4326_ = lean_nat_sub(v_x_4287_, v_one_4325_);
v___x_4327_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4322_, v_n_4326_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
lean_dec(v_n_4326_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4336_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4336_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4336_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4332_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4328_, v_binderType_4321_);
lean_dec_ref(v_binderType_4321_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4332_);
v___x_4334_ = v___x_4330_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
else
{
lean_dec_ref(v_binderType_4321_);
return v___x_4327_;
}
}
}
case 8:
{
lean_object* v_type_4337_; lean_object* v_body_4338_; lean_object* v___x_4339_; 
v_type_4337_ = lean_ctor_get(v_x_4286_, 1);
lean_inc_ref(v_type_4337_);
v_body_4338_ = lean_ctor_get(v_x_4286_, 3);
lean_inc_ref(v_body_4338_);
lean_dec_ref_known(v_x_4286_, 4);
v___x_4339_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4338_, v_x_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4348_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4342_ = v___x_4339_;
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4339_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4344_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4340_, v_type_4337_);
lean_dec_ref(v_type_4337_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v___x_4344_);
v___x_4346_ = v___x_4342_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
else
{
lean_dec_ref(v_type_4337_);
return v___x_4339_;
}
}
case 10:
{
lean_object* v_expr_4349_; 
v_expr_4349_ = lean_ctor_get(v_x_4286_, 1);
lean_inc_ref(v_expr_4349_);
lean_dec_ref_known(v_x_4286_, 2);
v_x_4286_ = v_expr_4349_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_deBruijnIndex_4351_ = lean_ctor_get(v_x_4286_, 0);
lean_inc(v_deBruijnIndex_4351_);
lean_dec_ref_known(v_x_4286_, 1);
v___x_4352_ = lean_unsigned_to_nat(0u);
v___x_4353_ = lean_nat_dec_eq(v_x_4287_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_dec(v_deBruijnIndex_4351_);
goto v___jp_4318_;
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_deBruijnIndex_4351_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
}
default: 
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_nat_dec_eq(v_x_4287_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_dec_ref(v_x_4286_);
goto v___jp_4318_;
}
else
{
v_type_4294_ = v_x_4286_;
v___y_4295_ = v_a_4288_;
v___y_4296_ = v_a_4289_;
v___y_4297_ = v_a_4290_;
v___y_4298_ = v_a_4291_;
goto v___jp_4293_;
}
}
}
v___jp_4293_:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_Meta_isPropQuick(v_type_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4309_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4309_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4309_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4304_ = lean_unbox(v_a_4300_);
lean_dec(v_a_4300_);
v___x_4305_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4304_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v___x_4305_);
v___x_4307_ = v___x_4302_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_a_4310_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4299_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4299_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
v___jp_4318_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_box(2);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4358_, lean_object* v_x_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4358_, v_x_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_x_4359_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4366_, lean_object* v_n_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4366_, v_n_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4383_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4383_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4383_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
uint8_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4378_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4374_);
lean_dec(v_a_4374_);
v___x_4379_ = lean_box(v___x_4378_);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 0, v___x_4379_);
v___x_4381_ = v___x_4376_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4373_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4373_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4392_, lean_object* v_n_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4392_, v_n_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_n_4393_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4400_, lean_object* v_x_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
switch(lean_obj_tag(v_x_4400_))
{
case 4:
{
lean_object* v_declName_4407_; lean_object* v_us_4408_; lean_object* v___x_4409_; 
v_declName_4407_ = lean_ctor_get(v_x_4400_, 0);
lean_inc(v_declName_4407_);
v_us_4408_ = lean_ctor_get(v_x_4400_, 1);
lean_inc(v_us_4408_);
lean_dec_ref_known(v_x_4400_, 2);
v___x_4409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4407_, v_us_4408_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4410_, v_x_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_x_4401_);
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_x_4401_);
v_a_4412_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4409_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4409_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4420_; lean_object* v___x_4421_; 
v_fvarId_4420_ = lean_ctor_get(v_x_4400_, 0);
lean_inc(v_fvarId_4420_);
lean_dec_ref_known(v_x_4400_, 1);
v___x_4421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4420_, v_a_4402_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4422_, v_x_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_x_4401_);
return v___x_4423_;
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_x_4401_);
v_a_4424_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4421_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4421_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4432_; lean_object* v___x_4433_; 
v_mvarId_4432_ = lean_ctor_get(v_x_4400_, 0);
lean_inc(v_mvarId_4432_);
lean_dec_ref_known(v_x_4400_, 1);
v___x_4433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4432_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4434_, v_x_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_x_4401_);
return v___x_4435_;
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_x_4401_);
v_a_4436_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4433_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4433_);
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
case 5:
{
lean_object* v_fn_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_fn_4444_ = lean_ctor_get(v_x_4400_, 0);
lean_inc_ref(v_fn_4444_);
lean_dec_ref_known(v_x_4400_, 2);
v___x_4445_ = lean_unsigned_to_nat(1u);
v___x_4446_ = lean_nat_add(v_x_4401_, v___x_4445_);
lean_dec(v_x_4401_);
v_x_4400_ = v_fn_4444_;
v_x_4401_ = v___x_4446_;
goto _start;
}
case 10:
{
lean_object* v_expr_4448_; 
v_expr_4448_ = lean_ctor_get(v_x_4400_, 1);
lean_inc_ref(v_expr_4448_);
lean_dec_ref_known(v_x_4400_, 2);
v_x_4400_ = v_expr_4448_;
goto _start;
}
case 8:
{
lean_object* v_body_4450_; 
v_body_4450_ = lean_ctor_get(v_x_4400_, 3);
lean_inc_ref(v_body_4450_);
lean_dec_ref_known(v_x_4400_, 4);
v_x_4400_ = v_body_4450_;
goto _start;
}
case 6:
{
lean_object* v_body_4452_; lean_object* v_zero_4453_; uint8_t v_isZero_4454_; 
v_body_4452_ = lean_ctor_get(v_x_4400_, 2);
lean_inc_ref(v_body_4452_);
lean_dec_ref_known(v_x_4400_, 3);
v_zero_4453_ = lean_unsigned_to_nat(0u);
v_isZero_4454_ = lean_nat_dec_eq(v_x_4401_, v_zero_4453_);
if (v_isZero_4454_ == 1)
{
lean_object* v___x_4455_; 
lean_dec(v_x_4401_);
v___x_4455_ = l_Lean_Meta_isProofQuick(v_body_4452_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
return v___x_4455_;
}
else
{
lean_object* v_one_4456_; lean_object* v_n_4457_; 
v_one_4456_ = lean_unsigned_to_nat(1u);
v_n_4457_ = lean_nat_sub(v_x_4401_, v_one_4456_);
lean_dec(v_x_4401_);
v_x_4400_ = v_body_4452_;
v_x_4401_ = v_n_4457_;
goto _start;
}
}
default: 
{
uint8_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec(v_x_4401_);
lean_dec_ref(v_x_4400_);
v___x_4459_ = 2;
v___x_4460_ = lean_box(v___x_4459_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
switch(lean_obj_tag(v_x_4462_))
{
case 0:
{
uint8_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_dec_ref_known(v_x_4462_, 1);
v___x_4468_ = 2;
v___x_4469_ = lean_box(v___x_4468_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
case 1:
{
lean_object* v_fvarId_4471_; lean_object* v___x_4472_; 
v_fvarId_4471_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_fvarId_4471_);
lean_dec_ref_known(v_x_4462_, 1);
v___x_4472_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4471_, v_a_4463_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4473_, v___x_4474_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
return v___x_4475_;
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
v_a_4476_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4472_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4472_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4484_; lean_object* v___x_4485_; 
v_mvarId_4484_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_mvarId_4484_);
lean_dec_ref_known(v_x_4462_, 1);
v___x_4485_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4484_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = lean_unsigned_to_nat(0u);
v___x_4488_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4486_, v___x_4487_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
return v___x_4488_;
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
v_a_4489_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4485_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4485_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
case 4:
{
lean_object* v_declName_4497_; lean_object* v_us_4498_; lean_object* v___x_4499_; 
v_declName_4497_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_declName_4497_);
v_us_4498_ = lean_ctor_get(v_x_4462_, 1);
lean_inc(v_us_4498_);
lean_dec_ref_known(v_x_4462_, 2);
v___x_4499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4497_, v_us_4498_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4499_, 1);
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4500_, v___x_4501_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
return v___x_4502_;
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
v_a_4503_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4499_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4499_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
case 5:
{
lean_object* v_fn_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v_fn_4511_ = lean_ctor_get(v_x_4462_, 0);
lean_inc_ref(v_fn_4511_);
lean_dec_ref_known(v_x_4462_, 2);
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4511_, v___x_4512_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
return v___x_4513_;
}
case 6:
{
lean_object* v_body_4514_; 
v_body_4514_ = lean_ctor_get(v_x_4462_, 2);
lean_inc_ref(v_body_4514_);
lean_dec_ref_known(v_x_4462_, 3);
v_x_4462_ = v_body_4514_;
goto _start;
}
case 8:
{
lean_object* v_body_4516_; 
v_body_4516_ = lean_ctor_get(v_x_4462_, 3);
lean_inc_ref(v_body_4516_);
lean_dec_ref_known(v_x_4462_, 4);
v_x_4462_ = v_body_4516_;
goto _start;
}
case 10:
{
lean_object* v_expr_4518_; 
v_expr_4518_ = lean_ctor_get(v_x_4462_, 1);
lean_inc_ref(v_expr_4518_);
lean_dec_ref_known(v_x_4462_, 2);
v_x_4462_ = v_expr_4518_;
goto _start;
}
case 11:
{
uint8_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_dec_ref_known(v_x_4462_, 3);
v___x_4520_ = 2;
v___x_4521_ = lean_box(v___x_4520_);
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
default: 
{
uint8_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec_ref(v_x_4462_);
v___x_4523_ = 0;
v___x_4524_ = lean_box(v___x_4523_);
v___x_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
return v___x_4525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Meta_isProofQuick(v_x_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4533_, lean_object* v_x_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4533_, v_x_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; 
lean_inc_ref(v_e_4541_);
v___x_4547_ = l_Lean_Meta_isProofQuick(v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4574_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4550_ = v___x_4547_;
v_isShared_4551_ = v_isSharedCheck_4574_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4547_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4574_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_unbox(v_a_4548_);
lean_dec(v_a_4548_);
switch(v___x_4552_)
{
case 0:
{
uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4556_; 
lean_dec_ref(v_e_4541_);
v___x_4553_ = 0;
v___x_4554_ = lean_box(v___x_4553_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4554_);
v___x_4556_ = v___x_4550_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
case 1:
{
uint8_t v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4561_; 
lean_dec_ref(v_e_4541_);
v___x_4558_ = 1;
v___x_4559_ = lean_box(v___x_4558_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4559_);
v___x_4561_ = v___x_4550_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
default: 
{
lean_object* v___x_4563_; 
lean_del_object(v___x_4550_);
lean_inc(v_a_4545_);
lean_inc_ref(v_a_4544_);
lean_inc(v_a_4543_);
lean_inc_ref(v_a_4542_);
v___x_4563_ = lean_infer_type(v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = l_Lean_Meta_isProp(v_a_4564_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
return v___x_4565_;
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
v_a_4566_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4563_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4563_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec_ref(v_e_4541_);
v_a_4575_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4547_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4547_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_Meta_isProof(v_e_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4590_, lean_object* v_x_4591_){
_start:
{
switch(lean_obj_tag(v_x_4590_))
{
case 3:
{
lean_object* v___x_4597_; uint8_t v___x_4598_; 
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = lean_nat_dec_eq(v_x_4591_, v___x_4597_);
lean_dec(v_x_4591_);
if (v___x_4598_ == 0)
{
goto v___jp_4593_;
}
else
{
uint8_t v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = 1;
v___x_4600_ = lean_box(v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
case 7:
{
lean_object* v_body_4602_; lean_object* v_zero_4603_; uint8_t v_isZero_4604_; 
v_body_4602_ = lean_ctor_get(v_x_4590_, 2);
v_zero_4603_ = lean_unsigned_to_nat(0u);
v_isZero_4604_ = lean_nat_dec_eq(v_x_4591_, v_zero_4603_);
if (v_isZero_4604_ == 1)
{
uint8_t v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec(v_x_4591_);
v___x_4605_ = 0;
v___x_4606_ = lean_box(v___x_4605_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
return v___x_4607_;
}
else
{
lean_object* v_one_4608_; lean_object* v_n_4609_; 
v_one_4608_ = lean_unsigned_to_nat(1u);
v_n_4609_ = lean_nat_sub(v_x_4591_, v_one_4608_);
lean_dec(v_x_4591_);
v_x_4590_ = v_body_4602_;
v_x_4591_ = v_n_4609_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4611_; 
v_body_4611_ = lean_ctor_get(v_x_4590_, 3);
v_x_4590_ = v_body_4611_;
goto _start;
}
case 10:
{
lean_object* v_expr_4613_; 
v_expr_4613_ = lean_ctor_get(v_x_4590_, 1);
v_x_4590_ = v_expr_4613_;
goto _start;
}
default: 
{
lean_dec(v_x_4591_);
goto v___jp_4593_;
}
}
v___jp_4593_:
{
uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = 2;
v___x_4595_ = lean_box(v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4615_, lean_object* v_x_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4615_, v_x_4616_);
lean_dec_ref(v_x_4615_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4619_, lean_object* v_x_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4619_, v_x_4620_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4627_, lean_object* v_x_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4627_, v_x_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec_ref(v_x_4627_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4635_, lean_object* v_x_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
switch(lean_obj_tag(v_x_4635_))
{
case 4:
{
lean_object* v_declName_4642_; lean_object* v_us_4643_; lean_object* v___x_4644_; 
v_declName_4642_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_declName_4642_);
v_us_4643_ = lean_ctor_get(v_x_4635_, 1);
lean_inc(v_us_4643_);
lean_dec_ref_known(v_x_4635_, 2);
v___x_4644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4642_, v_us_4643_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4645_, v_x_4636_);
lean_dec(v_a_4645_);
return v___x_4646_;
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_x_4636_);
v_a_4647_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4644_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4644_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4655_; lean_object* v___x_4656_; 
v_fvarId_4655_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_fvarId_4655_);
lean_dec_ref_known(v_x_4635_, 1);
v___x_4656_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4655_, v_a_4637_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref_known(v___x_4656_, 1);
v___x_4658_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4657_, v_x_4636_);
lean_dec(v_a_4657_);
return v___x_4658_;
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v_x_4636_);
v_a_4659_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4656_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4656_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4667_; lean_object* v___x_4668_; 
v_mvarId_4667_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_mvarId_4667_);
lean_dec_ref_known(v_x_4635_, 1);
v___x_4668_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4667_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4670_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4668_, 1);
v___x_4670_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4669_, v_x_4636_);
lean_dec(v_a_4669_);
return v___x_4670_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v_x_4636_);
v_a_4671_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4668_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4668_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
case 5:
{
lean_object* v_fn_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v_fn_4679_ = lean_ctor_get(v_x_4635_, 0);
lean_inc_ref(v_fn_4679_);
lean_dec_ref_known(v_x_4635_, 2);
v___x_4680_ = lean_unsigned_to_nat(1u);
v___x_4681_ = lean_nat_add(v_x_4636_, v___x_4680_);
lean_dec(v_x_4636_);
v_x_4635_ = v_fn_4679_;
v_x_4636_ = v___x_4681_;
goto _start;
}
case 10:
{
lean_object* v_expr_4683_; 
v_expr_4683_ = lean_ctor_get(v_x_4635_, 1);
lean_inc_ref(v_expr_4683_);
lean_dec_ref_known(v_x_4635_, 2);
v_x_4635_ = v_expr_4683_;
goto _start;
}
case 8:
{
lean_object* v_body_4685_; 
v_body_4685_ = lean_ctor_get(v_x_4635_, 3);
lean_inc_ref(v_body_4685_);
lean_dec_ref_known(v_x_4635_, 4);
v_x_4635_ = v_body_4685_;
goto _start;
}
case 6:
{
lean_object* v_body_4687_; lean_object* v_zero_4688_; uint8_t v_isZero_4689_; 
v_body_4687_ = lean_ctor_get(v_x_4635_, 2);
lean_inc_ref(v_body_4687_);
lean_dec_ref_known(v_x_4635_, 3);
v_zero_4688_ = lean_unsigned_to_nat(0u);
v_isZero_4689_ = lean_nat_dec_eq(v_x_4636_, v_zero_4688_);
if (v_isZero_4689_ == 1)
{
uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
lean_dec_ref(v_body_4687_);
lean_dec(v_x_4636_);
v___x_4690_ = 0;
v___x_4691_ = lean_box(v___x_4690_);
v___x_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
return v___x_4692_;
}
else
{
lean_object* v_one_4693_; lean_object* v_n_4694_; 
v_one_4693_ = lean_unsigned_to_nat(1u);
v_n_4694_ = lean_nat_sub(v_x_4636_, v_one_4693_);
lean_dec(v_x_4636_);
v_x_4635_ = v_body_4687_;
v_x_4636_ = v_n_4694_;
goto _start;
}
}
default: 
{
uint8_t v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
lean_dec(v_x_4636_);
lean_dec_ref(v_x_4635_);
v___x_4696_ = 2;
v___x_4697_ = lean_box(v___x_4696_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4699_, lean_object* v_x_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4699_, v_x_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
switch(lean_obj_tag(v_x_4707_))
{
case 1:
{
lean_object* v_fvarId_4713_; lean_object* v___x_4714_; 
v_fvarId_4713_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_fvarId_4713_);
lean_dec_ref_known(v_x_4707_, 1);
v___x_4714_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4713_, v_a_4708_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref_known(v___x_4714_, 1);
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4715_, v___x_4716_);
lean_dec(v_a_4715_);
return v___x_4717_;
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_a_4718_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4714_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4714_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4726_; lean_object* v___x_4727_; 
v_mvarId_4726_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_mvarId_4726_);
lean_dec_ref_known(v_x_4707_, 1);
v___x_4727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4726_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4728_, v___x_4729_);
lean_dec(v_a_4728_);
return v___x_4730_;
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4731_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4727_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4727_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
case 3:
{
uint8_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_dec_ref_known(v_x_4707_, 1);
v___x_4739_ = 1;
v___x_4740_ = lean_box(v___x_4739_);
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
return v___x_4741_;
}
case 4:
{
lean_object* v_declName_4742_; lean_object* v_us_4743_; lean_object* v___x_4744_; 
v_declName_4742_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_declName_4742_);
v_us_4743_ = lean_ctor_get(v_x_4707_, 1);
lean_inc(v_us_4743_);
lean_dec_ref_known(v_x_4707_, 2);
v___x_4744_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4742_, v_us_4743_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4745_, v___x_4746_);
lean_dec(v_a_4745_);
return v___x_4747_;
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
v_a_4748_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4744_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4744_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
case 5:
{
lean_object* v_fn_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_fn_4756_ = lean_ctor_get(v_x_4707_, 0);
lean_inc_ref(v_fn_4756_);
lean_dec_ref_known(v_x_4707_, 2);
v___x_4757_ = lean_unsigned_to_nat(1u);
v___x_4758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4756_, v___x_4757_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v___x_4758_;
}
case 6:
{
uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec_ref_known(v_x_4707_, 3);
v___x_4759_ = 0;
v___x_4760_ = lean_box(v___x_4759_);
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4760_);
return v___x_4761_;
}
case 7:
{
uint8_t v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
lean_dec_ref_known(v_x_4707_, 3);
v___x_4762_ = 1;
v___x_4763_ = lean_box(v___x_4762_);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
case 8:
{
lean_object* v_body_4765_; 
v_body_4765_ = lean_ctor_get(v_x_4707_, 3);
lean_inc_ref(v_body_4765_);
lean_dec_ref_known(v_x_4707_, 4);
v_x_4707_ = v_body_4765_;
goto _start;
}
case 9:
{
uint8_t v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec_ref_known(v_x_4707_, 1);
v___x_4767_ = 0;
v___x_4768_ = lean_box(v___x_4767_);
v___x_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
return v___x_4769_;
}
case 10:
{
lean_object* v_expr_4770_; 
v_expr_4770_ = lean_ctor_get(v_x_4707_, 1);
lean_inc_ref(v_expr_4770_);
lean_dec_ref_known(v_x_4707_, 2);
v_x_4707_ = v_expr_4770_;
goto _start;
}
default: 
{
uint8_t v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_dec_ref(v_x_4707_);
v___x_4772_ = 2;
v___x_4773_ = lean_box(v___x_4772_);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_Meta_isTypeQuick(v_x_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; 
lean_inc_ref(v_e_4782_);
v___x_4788_ = l_Lean_Meta_isTypeQuick(v_e_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4838_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4838_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4838_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
uint8_t v___x_4793_; 
v___x_4793_ = lean_unbox(v_a_4789_);
lean_dec(v_a_4789_);
switch(v___x_4793_)
{
case 0:
{
uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_dec_ref(v_e_4782_);
v___x_4794_ = 0;
v___x_4795_ = lean_box(v___x_4794_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4795_);
v___x_4797_ = v___x_4791_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
case 1:
{
uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
lean_dec_ref(v_e_4782_);
v___x_4799_ = 1;
v___x_4800_ = lean_box(v___x_4799_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4800_);
v___x_4802_ = v___x_4791_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
default: 
{
lean_object* v___x_4804_; 
lean_del_object(v___x_4791_);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc_ref(v_a_4783_);
v___x_4804_ = lean_infer_type(v_e_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4806_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v___x_4806_ = l_Lean_Meta_whnfD(v_a_4805_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4821_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 3)
{
uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4814_; 
lean_dec_ref_known(v_a_4807_, 1);
v___x_4811_ = 1;
v___x_4812_ = lean_box(v___x_4811_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4812_);
v___x_4814_ = v___x_4809_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
else
{
uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4819_; 
lean_dec(v_a_4807_);
v___x_4816_ = 0;
v___x_4817_ = lean_box(v___x_4816_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4817_);
v___x_4819_ = v___x_4809_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
v_a_4822_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4806_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4806_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
v_a_4830_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4804_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4804_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec_ref(v_e_4782_);
v_a_4839_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4788_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4788_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_isType(v_e_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4854_){
_start:
{
switch(lean_obj_tag(v_x_4854_))
{
case 7:
{
lean_object* v_body_4855_; 
v_body_4855_ = lean_ctor_get(v_x_4854_, 2);
v_x_4854_ = v_body_4855_;
goto _start;
}
case 3:
{
lean_object* v_u_4857_; lean_object* v___x_4858_; 
v_u_4857_ = lean_ctor_get(v_x_4854_, 0);
lean_inc(v_u_4857_);
v___x_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4858_, 0, v_u_4857_);
return v___x_4858_;
}
default: 
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_box(0);
return v___x_4859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4860_);
lean_dec_ref(v_x_4860_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4862_, lean_object* v_body_4863_, lean_object* v_x_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4862_, v_body_4863_, v_x_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4873_, lean_object* v_xs_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
switch(lean_obj_tag(v_type_4873_))
{
case 3:
{
lean_object* v_u_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v_xs_4874_);
v_u_4880_ = lean_ctor_get(v_type_4873_, 0);
lean_inc(v_u_4880_);
lean_dec_ref_known(v_type_4873_, 1);
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_u_4880_);
v___x_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
return v___x_4882_;
}
case 7:
{
lean_object* v_binderName_4883_; lean_object* v_binderType_4884_; lean_object* v_body_4885_; uint8_t v_binderInfo_4886_; lean_object* v___f_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v_binderName_4883_ = lean_ctor_get(v_type_4873_, 0);
lean_inc(v_binderName_4883_);
v_binderType_4884_ = lean_ctor_get(v_type_4873_, 1);
lean_inc_ref(v_binderType_4884_);
v_body_4885_ = lean_ctor_get(v_type_4873_, 2);
lean_inc_ref(v_body_4885_);
v_binderInfo_4886_ = lean_ctor_get_uint8(v_type_4873_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4873_, 3);
lean_inc_ref(v_xs_4874_);
v___f_4887_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4887_, 0, v_xs_4874_);
lean_closure_set(v___f_4887_, 1, v_body_4885_);
v___x_4888_ = lean_expr_instantiate_rev(v_binderType_4884_, v_xs_4874_);
lean_dec_ref(v_xs_4874_);
lean_dec_ref(v_binderType_4884_);
v___x_4889_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4883_, v_binderInfo_4886_, v___x_4888_, v___f_4887_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
return v___x_4889_;
}
default: 
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_expr_instantiate_rev(v_type_4873_, v_xs_4874_);
lean_dec_ref(v_xs_4874_);
lean_dec_ref(v_type_4873_);
v___x_4891_ = l_Lean_Meta_whnfD(v___x_4890_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4907_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4907_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4907_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
switch(lean_obj_tag(v_a_4892_))
{
case 3:
{
lean_object* v_u_4896_; lean_object* v___x_4897_; lean_object* v___x_4899_; 
v_u_4896_ = lean_ctor_get(v_a_4892_, 0);
lean_inc(v_u_4896_);
lean_dec_ref_known(v_a_4892_, 1);
v___x_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4897_, 0, v_u_4896_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4897_);
v___x_4899_ = v___x_4894_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4897_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
case 7:
{
lean_object* v___x_4901_; 
lean_del_object(v___x_4894_);
v___x_4901_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4873_ = v_a_4892_;
v_xs_4874_ = v___x_4901_;
goto _start;
}
default: 
{
lean_object* v___x_4903_; lean_object* v___x_4905_; 
lean_dec(v_a_4892_);
v___x_4903_ = lean_box(0);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4903_);
v___x_4905_ = v___x_4894_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
else
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4915_; 
v_a_4908_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4910_ = v___x_4891_;
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4891_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4915_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4913_; 
if (v_isShared_4911_ == 0)
{
v___x_4913_ = v___x_4910_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4908_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4916_, lean_object* v_body_4917_, lean_object* v_x_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = lean_array_push(v_xs_4916_, v_x_4918_);
v___x_4925_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4917_, v___x_4924_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4926_, lean_object* v_xs_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4926_, v_xs_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4934_, lean_object* v_cache_4935_, lean_object* v_a_x3f_4936_){
_start:
{
lean_object* v___x_4938_; lean_object* v_mctx_4939_; lean_object* v_zetaDeltaFVarIds_4940_; lean_object* v_postponed_4941_; lean_object* v_diag_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4952_; 
v___x_4938_ = lean_st_ref_take(v_a_4934_);
v_mctx_4939_ = lean_ctor_get(v___x_4938_, 0);
v_zetaDeltaFVarIds_4940_ = lean_ctor_get(v___x_4938_, 2);
v_postponed_4941_ = lean_ctor_get(v___x_4938_, 3);
v_diag_4942_ = lean_ctor_get(v___x_4938_, 4);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4952_ == 0)
{
lean_object* v_unused_4953_; 
v_unused_4953_ = lean_ctor_get(v___x_4938_, 1);
lean_dec(v_unused_4953_);
v___x_4944_ = v___x_4938_;
v_isShared_4945_ = v_isSharedCheck_4952_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_diag_4942_);
lean_inc(v_postponed_4941_);
lean_inc(v_zetaDeltaFVarIds_4940_);
lean_inc(v_mctx_4939_);
lean_dec(v___x_4938_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4952_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 1, v_cache_4935_);
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_mctx_4939_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_cache_4935_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_zetaDeltaFVarIds_4940_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_postponed_4941_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v_diag_4942_);
v___x_4947_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = lean_st_ref_put(v_a_4934_, v___x_4947_);
v___x_4949_ = lean_box(0);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
return v___x_4950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4954_, lean_object* v_cache_4955_, lean_object* v_a_x3f_4956_, lean_object* v___y_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4954_, v_cache_4955_, v_a_x3f_4956_);
lean_dec(v_a_x3f_4956_);
lean_dec(v_a_4954_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4959_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v___x_4966_; lean_object* v_cache_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4966_ = lean_st_ref_get(v_a_4961_);
v_cache_4967_ = lean_ctor_get(v___x_4966_, 1);
lean_inc_ref(v_cache_4967_);
lean_dec(v___x_4966_);
v___x_4968_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4969_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4959_, v___x_4968_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4986_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4972_ = v___x_4969_;
v_isShared_4973_ = v_isSharedCheck_4986_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4969_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4986_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
lean_inc(v_a_4970_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 1);
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
v___x_4976_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4961_, v_cache_4967_, v___x_4975_);
lean_dec_ref(v___x_4975_);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4983_ == 0)
{
lean_object* v_unused_4984_; 
v_unused_4984_ = lean_ctor_get(v___x_4976_, 0);
lean_dec(v_unused_4984_);
v___x_4978_ = v___x_4976_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_dec(v___x_4976_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
lean_ctor_set(v___x_4978_, 0, v_a_4970_);
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4970_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
v_a_4987_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4969_, 1);
v___x_4988_ = lean_box(0);
v___x_4989_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4961_, v_cache_4967_, v___x_4988_);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v___x_4989_, 0);
lean_dec(v_unused_4997_);
v___x_4991_ = v___x_4989_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_dec(v___x_4989_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 1);
lean_ctor_set(v___x_4991_, 0, v_a_4987_);
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4987_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v___x_4998_; 
lean_dec_ref(v_type_4959_);
v___x_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4965_);
return v___x_4998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5027_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5027_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5027_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
if (lean_obj_tag(v_a_5013_) == 0)
{
uint8_t v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5017_ = 0;
v___x_5018_ = lean_box(v___x_5017_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5018_);
v___x_5020_ = v___x_5015_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
else
{
uint8_t v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
lean_dec_ref_known(v_a_5013_, 1);
v___x_5022_ = 1;
v___x_5023_ = lean_box(v___x_5022_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5023_);
v___x_5025_ = v___x_5015_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
v_a_5028_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5012_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5012_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_Meta_isTypeFormerType(v_type_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
return v_res_5042_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5043_, lean_object* v_x_5044_){
_start:
{
if (lean_obj_tag(v_x_5043_) == 0)
{
if (lean_obj_tag(v_x_5044_) == 0)
{
uint8_t v___x_5045_; 
v___x_5045_ = 1;
return v___x_5045_;
}
else
{
uint8_t v___x_5046_; 
v___x_5046_ = 0;
return v___x_5046_;
}
}
else
{
if (lean_obj_tag(v_x_5044_) == 0)
{
uint8_t v___x_5047_; 
v___x_5047_ = 0;
return v___x_5047_;
}
else
{
lean_object* v_val_5048_; lean_object* v_val_5049_; uint8_t v___x_5050_; 
v_val_5048_ = lean_ctor_get(v_x_5043_, 0);
v_val_5049_ = lean_ctor_get(v_x_5044_, 0);
v___x_5050_ = lean_level_eq(v_val_5048_, v_val_5049_);
return v___x_5050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5051_, lean_object* v_x_5052_){
_start:
{
uint8_t v_res_5053_; lean_object* v_r_5054_; 
v_res_5053_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5051_, v_x_5052_);
lean_dec(v_x_5052_);
lean_dec(v_x_5051_);
v_r_5054_ = lean_box(v_res_5053_);
return v_r_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5074_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5066_ = v___x_5063_;
v_isShared_5067_ = v_isSharedCheck_5074_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5063_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5074_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5068_; uint8_t v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5072_; 
v___x_5068_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5069_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5064_, v___x_5068_);
lean_dec(v_a_5064_);
v___x_5070_ = lean_box(v___x_5069_);
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v___x_5070_);
v___x_5072_ = v___x_5066_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5070_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
v_a_5075_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5063_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5063_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_Meta_isPropFormerType(v_type_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_);
lean_dec(v_a_5087_);
lean_dec_ref(v_a_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v___x_5096_; 
lean_inc(v_a_5094_);
lean_inc_ref(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc_ref(v_a_5091_);
v___x_5096_ = lean_infer_type(v_e_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5098_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5097_);
lean_dec_ref_known(v___x_5096_, 1);
v___x_5098_ = l_Lean_Meta_isTypeFormerType(v_a_5097_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
return v___x_5098_;
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
v_a_5099_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v___x_5096_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5096_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_isTypeFormer(v_e_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5114_, lean_object* v_maxFVars_x3f_5115_, lean_object* v_k_5116_, uint8_t v_cleanupAnnotations_5117_, uint8_t v_whnfType_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v___f_5124_; lean_object* v___x_5125_; 
v___f_5124_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5124_, 0, v_k_5116_);
v___x_5125_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5114_, v_maxFVars_x3f_5115_, v___f_5124_, v_cleanupAnnotations_5117_, v_whnfType_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
else
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
v_a_5134_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5125_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5125_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5142_, lean_object* v_maxFVars_x3f_5143_, lean_object* v_k_5144_, lean_object* v_cleanupAnnotations_5145_, lean_object* v_whnfType_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5152_; uint8_t v_whnfType_boxed_5153_; lean_object* v_res_5154_; 
v_cleanupAnnotations_boxed_5152_ = lean_unbox(v_cleanupAnnotations_5145_);
v_whnfType_boxed_5153_ = lean_unbox(v_whnfType_5146_);
v_res_5154_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5142_, v_maxFVars_x3f_5143_, v_k_5144_, v_cleanupAnnotations_boxed_5152_, v_whnfType_boxed_5153_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5155_, lean_object* v_type_5156_, lean_object* v_maxFVars_x3f_5157_, lean_object* v_k_5158_, uint8_t v_cleanupAnnotations_5159_, uint8_t v_whnfType_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5156_, v_maxFVars_x3f_5157_, v_k_5158_, v_cleanupAnnotations_5159_, v_whnfType_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5167_, lean_object* v_type_5168_, lean_object* v_maxFVars_x3f_5169_, lean_object* v_k_5170_, lean_object* v_cleanupAnnotations_5171_, lean_object* v_whnfType_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5178_; uint8_t v_whnfType_boxed_5179_; lean_object* v_res_5180_; 
v_cleanupAnnotations_boxed_5178_ = lean_unbox(v_cleanupAnnotations_5171_);
v_whnfType_boxed_5179_ = lean_unbox(v_whnfType_5172_);
v_res_5180_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5167_, v_type_5168_, v_maxFVars_x3f_5169_, v_k_5170_, v_cleanupAnnotations_boxed_5178_, v_whnfType_boxed_5179_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
return v_res_5180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5181_, lean_object* v_as_5182_, size_t v_i_5183_, size_t v_stop_5184_){
_start:
{
uint8_t v___x_5185_; 
v___x_5185_ = lean_usize_dec_eq(v_i_5183_, v_stop_5184_);
if (v___x_5185_ == 0)
{
lean_object* v___x_5186_; uint8_t v___x_5187_; 
v___x_5186_ = lean_array_uget_borrowed(v_as_5182_, v_i_5183_);
v___x_5187_ = lean_expr_eqv(v_a_5181_, v___x_5186_);
if (v___x_5187_ == 0)
{
size_t v___x_5188_; size_t v___x_5189_; 
v___x_5188_ = ((size_t)1ULL);
v___x_5189_ = lean_usize_add(v_i_5183_, v___x_5188_);
v_i_5183_ = v___x_5189_;
goto _start;
}
else
{
return v___x_5187_;
}
}
else
{
uint8_t v___x_5191_; 
v___x_5191_ = 0;
return v___x_5191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5192_, lean_object* v_as_5193_, lean_object* v_i_5194_, lean_object* v_stop_5195_){
_start:
{
size_t v_i_boxed_5196_; size_t v_stop_boxed_5197_; uint8_t v_res_5198_; lean_object* v_r_5199_; 
v_i_boxed_5196_ = lean_unbox_usize(v_i_5194_);
lean_dec(v_i_5194_);
v_stop_boxed_5197_ = lean_unbox_usize(v_stop_5195_);
lean_dec(v_stop_5195_);
v_res_5198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5192_, v_as_5193_, v_i_boxed_5196_, v_stop_boxed_5197_);
lean_dec_ref(v_as_5193_);
lean_dec_ref(v_a_5192_);
v_r_5199_ = lean_box(v_res_5198_);
return v_r_5199_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; 
v___x_5202_ = lean_unsigned_to_nat(0u);
v___x_5203_ = lean_array_get_size(v_as_5200_);
v___x_5204_ = lean_nat_dec_lt(v___x_5202_, v___x_5203_);
if (v___x_5204_ == 0)
{
return v___x_5204_;
}
else
{
if (v___x_5204_ == 0)
{
return v___x_5204_;
}
else
{
size_t v___x_5205_; size_t v___x_5206_; uint8_t v___x_5207_; 
v___x_5205_ = ((size_t)0ULL);
v___x_5206_ = lean_usize_of_nat(v___x_5203_);
v___x_5207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5201_, v_as_5200_, v___x_5205_, v___x_5206_);
return v___x_5207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5208_, lean_object* v_a_5209_){
_start:
{
uint8_t v_res_5210_; lean_object* v_r_5211_; 
v_res_5210_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5208_, v_a_5209_);
lean_dec_ref(v_a_5209_);
lean_dec_ref(v_as_5208_);
v_r_5211_ = lean_box(v_res_5210_);
return v_r_5211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5212_, lean_object* v_e_5213_){
_start:
{
uint8_t v___x_5214_; lean_object* v_d_5216_; lean_object* v_b_5217_; 
v___x_5214_ = l_Lean_Expr_hasFVar(v_e_5213_);
if (v___x_5214_ == 0)
{
lean_dec_ref(v_e_5213_);
return v___x_5214_;
}
else
{
switch(lean_obj_tag(v_e_5213_))
{
case 7:
{
lean_object* v_binderType_5220_; lean_object* v_body_5221_; 
v_binderType_5220_ = lean_ctor_get(v_e_5213_, 1);
lean_inc_ref(v_binderType_5220_);
v_body_5221_ = lean_ctor_get(v_e_5213_, 2);
lean_inc_ref(v_body_5221_);
lean_dec_ref_known(v_e_5213_, 3);
v_d_5216_ = v_binderType_5220_;
v_b_5217_ = v_body_5221_;
goto v___jp_5215_;
}
case 6:
{
lean_object* v_binderType_5222_; lean_object* v_body_5223_; 
v_binderType_5222_ = lean_ctor_get(v_e_5213_, 1);
lean_inc_ref(v_binderType_5222_);
v_body_5223_ = lean_ctor_get(v_e_5213_, 2);
lean_inc_ref(v_body_5223_);
lean_dec_ref_known(v_e_5213_, 3);
v_d_5216_ = v_binderType_5222_;
v_b_5217_ = v_body_5223_;
goto v___jp_5215_;
}
case 10:
{
lean_object* v_expr_5224_; 
v_expr_5224_ = lean_ctor_get(v_e_5213_, 1);
lean_inc_ref(v_expr_5224_);
lean_dec_ref_known(v_e_5213_, 2);
v_e_5213_ = v_expr_5224_;
goto _start;
}
case 8:
{
lean_object* v_type_5226_; lean_object* v_value_5227_; lean_object* v_body_5228_; uint8_t v___x_5229_; 
v_type_5226_ = lean_ctor_get(v_e_5213_, 1);
lean_inc_ref(v_type_5226_);
v_value_5227_ = lean_ctor_get(v_e_5213_, 2);
lean_inc_ref(v_value_5227_);
v_body_5228_ = lean_ctor_get(v_e_5213_, 3);
lean_inc_ref(v_body_5228_);
lean_dec_ref_known(v_e_5213_, 4);
v___x_5229_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5212_, v_type_5226_);
if (v___x_5229_ == 0)
{
uint8_t v___x_5230_; 
v___x_5230_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5212_, v_value_5227_);
if (v___x_5230_ == 0)
{
v_e_5213_ = v_body_5228_;
goto _start;
}
else
{
lean_dec_ref(v_body_5228_);
return v___x_5214_;
}
}
else
{
lean_dec_ref(v_body_5228_);
lean_dec_ref(v_value_5227_);
return v___x_5214_;
}
}
case 5:
{
lean_object* v_fn_5232_; lean_object* v_arg_5233_; uint8_t v___x_5234_; 
v_fn_5232_ = lean_ctor_get(v_e_5213_, 0);
lean_inc_ref(v_fn_5232_);
v_arg_5233_ = lean_ctor_get(v_e_5213_, 1);
lean_inc_ref(v_arg_5233_);
lean_dec_ref_known(v_e_5213_, 2);
v___x_5234_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5212_, v_fn_5232_);
if (v___x_5234_ == 0)
{
v_e_5213_ = v_arg_5233_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5233_);
return v___x_5214_;
}
}
case 11:
{
lean_object* v_struct_5236_; 
v_struct_5236_ = lean_ctor_get(v_e_5213_, 2);
lean_inc_ref(v_struct_5236_);
lean_dec_ref_known(v_e_5213_, 3);
v_e_5213_ = v_struct_5236_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5238_; lean_object* v___x_5239_; uint8_t v___x_5240_; 
v_fvarId_5238_ = lean_ctor_get(v_e_5213_, 0);
lean_inc(v_fvarId_5238_);
lean_dec_ref_known(v_e_5213_, 1);
v___x_5239_ = l_Lean_Expr_fvar___override(v_fvarId_5238_);
v___x_5240_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5212_, v___x_5239_);
lean_dec_ref(v___x_5239_);
return v___x_5240_;
}
default: 
{
uint8_t v___x_5241_; 
lean_dec_ref(v_e_5213_);
v___x_5241_ = 0;
return v___x_5241_;
}
}
}
v___jp_5215_:
{
uint8_t v___x_5218_; 
v___x_5218_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5212_, v_d_5216_);
if (v___x_5218_ == 0)
{
v_e_5213_ = v_b_5217_;
goto _start;
}
else
{
lean_dec_ref(v_b_5217_);
return v___x_5214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5242_, lean_object* v_e_5243_){
_start:
{
uint8_t v_res_5244_; lean_object* v_r_5245_; 
v_res_5244_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5242_, v_e_5243_);
lean_dec_ref(v_xs_5242_);
v_r_5245_ = lean_box(v_res_5244_);
return v_r_5245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5248_ = l_Lean_stringToMessageData(v___x_5247_);
return v___x_5248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5251_ = l_Lean_stringToMessageData(v___x_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5252_, lean_object* v_type_5253_, lean_object* v_as_5254_, size_t v_sz_5255_, size_t v_i_5256_, lean_object* v_b_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_a_5264_; uint8_t v___x_5268_; 
v___x_5268_ = lean_usize_dec_lt(v_i_5256_, v_sz_5255_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5269_; 
lean_dec_ref(v_type_5253_);
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v_b_5257_);
return v___x_5269_;
}
else
{
lean_object* v___x_5270_; lean_object* v_a_5271_; uint8_t v___x_5272_; 
v___x_5270_ = lean_box(0);
v_a_5271_ = lean_array_uget_borrowed(v_as_5254_, v_i_5256_);
lean_inc(v_a_5271_);
v___x_5272_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5252_, v_a_5271_);
if (v___x_5272_ == 0)
{
v_a_5264_ = v___x_5270_;
goto v___jp_5263_;
}
else
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5271_);
v___x_5274_ = l_Lean_MessageData_ofExpr(v_a_5271_);
v___x_5275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5273_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5275_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
lean_inc_ref(v_type_5253_);
v___x_5278_ = l_Lean_MessageData_ofExpr(v_type_5253_);
v___x_5279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5277_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5279_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_dec_ref_known(v___x_5280_, 1);
v_a_5264_ = v___x_5270_;
goto v___jp_5263_;
}
else
{
lean_dec_ref(v_type_5253_);
return v___x_5280_;
}
}
}
v___jp_5263_:
{
size_t v___x_5265_; size_t v___x_5266_; 
v___x_5265_ = ((size_t)1ULL);
v___x_5266_ = lean_usize_add(v_i_5256_, v___x_5265_);
v_i_5256_ = v___x_5266_;
v_b_5257_ = v_a_5264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5281_, lean_object* v_type_5282_, lean_object* v_as_5283_, lean_object* v_sz_5284_, lean_object* v_i_5285_, lean_object* v_b_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
size_t v_sz_boxed_5292_; size_t v_i_boxed_5293_; lean_object* v_res_5294_; 
v_sz_boxed_5292_ = lean_unbox_usize(v_sz_5284_);
lean_dec(v_sz_5284_);
v_i_boxed_5293_ = lean_unbox_usize(v_i_5285_);
lean_dec(v_i_5285_);
v_res_5294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5281_, v_type_5282_, v_as_5283_, v_sz_boxed_5292_, v_i_boxed_5293_, v_b_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec_ref(v_as_5283_);
lean_dec_ref(v_xs_5281_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5295_, size_t v_i_5296_, lean_object* v_bs_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
uint8_t v___x_5303_; 
v___x_5303_ = lean_usize_dec_lt(v_i_5296_, v_sz_5295_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; 
v___x_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5304_, 0, v_bs_5297_);
return v___x_5304_;
}
else
{
lean_object* v_v_5305_; lean_object* v___x_5306_; 
v_v_5305_ = lean_array_uget_borrowed(v_bs_5297_, v_i_5296_);
lean_inc(v___y_5301_);
lean_inc_ref(v___y_5300_);
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
lean_inc(v_v_5305_);
v___x_5306_ = lean_infer_type(v_v_5305_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5308_; lean_object* v_bs_x27_5309_; size_t v___x_5310_; size_t v___x_5311_; lean_object* v___x_5312_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref_known(v___x_5306_, 1);
v___x_5308_ = lean_unsigned_to_nat(0u);
v_bs_x27_5309_ = lean_array_uset(v_bs_5297_, v_i_5296_, v___x_5308_);
v___x_5310_ = ((size_t)1ULL);
v___x_5311_ = lean_usize_add(v_i_5296_, v___x_5310_);
v___x_5312_ = lean_array_uset(v_bs_x27_5309_, v_i_5296_, v_a_5307_);
v_i_5296_ = v___x_5311_;
v_bs_5297_ = v___x_5312_;
goto _start;
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_dec_ref(v_bs_5297_);
v_a_5314_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5306_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5306_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5322_, lean_object* v_i_5323_, lean_object* v_bs_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
size_t v_sz_boxed_5330_; size_t v_i_boxed_5331_; lean_object* v_res_5332_; 
v_sz_boxed_5330_ = lean_unbox_usize(v_sz_5322_);
lean_dec(v_sz_5322_);
v_i_boxed_5331_ = lean_unbox_usize(v_i_5323_);
lean_dec(v_i_5323_);
v_res_5332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5330_, v_i_boxed_5331_, v_bs_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
return v_res_5332_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; 
v___x_5334_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5335_ = l_Lean_stringToMessageData(v___x_5334_);
return v___x_5335_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5337_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5338_ = l_Lean_stringToMessageData(v___x_5337_);
return v___x_5338_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; 
v___x_5340_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5341_ = l_Lean_stringToMessageData(v___x_5340_);
return v___x_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5342_, lean_object* v_n_5343_, lean_object* v_xs_5344_, lean_object* v_x_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v___x_5375_; uint8_t v___x_5376_; 
v___x_5375_ = lean_array_get_size(v_xs_5344_);
v___x_5376_ = lean_nat_dec_eq(v___x_5375_, v_n_5343_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec_ref(v_xs_5344_);
v___x_5377_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5378_ = l_Lean_MessageData_ofExpr(v_type_5342_);
v___x_5379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5379_, 0, v___x_5377_);
lean_ctor_set(v___x_5379_, 1, v___x_5378_);
v___x_5380_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5379_);
lean_ctor_set(v___x_5381_, 1, v___x_5380_);
v___x_5382_ = l_Nat_reprFast(v_n_5343_);
v___x_5383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5382_);
v___x_5384_ = l_Lean_MessageData_ofFormat(v___x_5383_);
v___x_5385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5381_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
v___x_5386_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5385_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5387_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5388_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5388_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
else
{
lean_dec(v_n_5343_);
goto v___jp_5351_;
}
v___jp_5351_:
{
size_t v_sz_5352_; size_t v___x_5353_; lean_object* v___x_5354_; 
v_sz_5352_ = lean_array_size(v_xs_5344_);
v___x_5353_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5344_);
v___x_5354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5352_, v___x_5353_, v_xs_5344_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
if (lean_obj_tag(v___x_5354_) == 0)
{
lean_object* v_a_5355_; lean_object* v___x_5356_; size_t v_sz_5357_; lean_object* v___x_5358_; 
v_a_5355_ = lean_ctor_get(v___x_5354_, 0);
lean_inc(v_a_5355_);
lean_dec_ref_known(v___x_5354_, 1);
v___x_5356_ = lean_box(0);
v_sz_5357_ = lean_array_size(v_a_5355_);
v___x_5358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5344_, v_type_5342_, v_a_5355_, v_sz_5357_, v___x_5353_, v___x_5356_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
lean_dec_ref(v_xs_5344_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5365_ == 0)
{
lean_object* v_unused_5366_; 
v_unused_5366_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5366_);
v___x_5360_ = v___x_5358_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_dec(v___x_5358_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v_a_5355_);
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5355_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec(v_a_5355_);
v_a_5367_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5358_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5358_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5344_);
lean_dec_ref(v_type_5342_);
return v___x_5354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5397_, lean_object* v_n_5398_, lean_object* v_xs_5399_, lean_object* v_x_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5397_, v_n_5398_, v_xs_5399_, v_x_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
lean_dec_ref(v_x_5400_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5407_, lean_object* v_type_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
lean_object* v___f_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; 
lean_inc(v_n_5407_);
lean_inc_ref(v_type_5408_);
v___f_5414_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5414_, 0, v_type_5408_);
lean_closure_set(v___f_5414_, 1, v_n_5407_);
v___x_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5415_, 0, v_n_5407_);
v___x_5416_ = 0;
v___x_5417_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5408_, v___x_5415_, v___f_5414_, v___x_5416_, v___x_5416_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5418_, lean_object* v_type_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l_Lean_Meta_arrowDomainsN(v_n_5418_, v_type_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
lean_dec(v_a_5423_);
lean_dec_ref(v_a_5422_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5426_, lean_object* v_e_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_){
_start:
{
lean_object* v___x_5433_; 
lean_inc(v_a_5431_);
lean_inc_ref(v_a_5430_);
lean_inc(v_a_5429_);
lean_inc_ref(v_a_5428_);
v___x_5433_ = lean_infer_type(v_e_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5435_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
lean_dec_ref_known(v___x_5433_, 1);
v___x_5435_ = l_Lean_Meta_arrowDomainsN(v_n_5426_, v_a_5434_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_);
return v___x_5435_;
}
else
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
lean_dec(v_n_5426_);
v_a_5436_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5438_ = v___x_5433_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5433_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5444_, lean_object* v_e_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_Meta_inferArgumentTypesN(v_n_5444_, v_e_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_);
lean_dec(v_a_5449_);
lean_dec_ref(v_a_5448_);
lean_dec(v_a_5447_);
lean_dec_ref(v_a_5446_);
return v_res_5451_;
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
