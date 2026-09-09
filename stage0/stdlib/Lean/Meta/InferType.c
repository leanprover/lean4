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
lean_object* v___x_683_; lean_object* v_env_684_; lean_object* v___x_685_; lean_object* v_toCold_686_; lean_object* v_mctx_687_; lean_object* v_lctx_688_; lean_object* v_options_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_683_ = lean_st_ref_get(v___y_681_);
v_env_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc_ref(v_env_684_);
lean_dec(v___x_683_);
v___x_685_ = lean_st_ref_get(v___y_679_);
v_toCold_686_ = lean_ctor_get(v___y_680_, 0);
v_mctx_687_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_mctx_687_);
lean_dec(v___x_685_);
v_lctx_688_ = lean_ctor_get(v___y_678_, 2);
v_options_689_ = lean_ctor_get(v_toCold_686_, 2);
lean_inc_ref(v_options_689_);
lean_inc_ref(v_lctx_688_);
v___x_690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_690_, 0, v_env_684_);
lean_ctor_set(v___x_690_, 1, v_mctx_687_);
lean_ctor_set(v___x_690_, 2, v_lctx_688_);
lean_ctor_set(v___x_690_, 3, v_options_689_);
v___x_691_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_msgData_677_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_ref_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_ref_706_ = lean_ctor_get(v___y_703_, 2);
v___x_707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_inc(v_ref_706_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_ref_706_);
lean_ctor_set(v___x_712_, 1, v_a_708_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 1);
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_726_ = l_Lean_stringToMessageData(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_733_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_734_ = l_Lean_indentExpr(v_f_727_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_735_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_744_, lean_object* v_f_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_752_, lean_object* v_f_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_752_, v_f_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_768_, lean_object* v_msg_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_768_, v_msg_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_776_, lean_object* v_args_777_, lean_object* v_f_778_, lean_object* v_a_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_a_787_; uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_lt(v_a_779_, v_upperBound_776_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v_a_779_);
lean_dec_ref(v_f_778_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_b_780_);
return v___x_792_;
}
else
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_b_780_, 0);
lean_inc(v_fst_793_);
if (lean_obj_tag(v_fst_793_) == 7)
{
lean_object* v_snd_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_snd_794_ = lean_ctor_get(v_b_780_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_b_780_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_b_780_, 0);
lean_dec(v_unused_803_);
v___x_796_ = v_b_780_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snd_794_);
lean_dec(v_b_780_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_body_798_; lean_object* v___x_800_; 
v_body_798_ = lean_ctor_get(v_fst_793_, 2);
lean_inc_ref(v_body_798_);
lean_dec_ref_known(v_fst_793_, 3);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_body_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_body_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_794_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_a_787_ = v___x_800_;
goto v___jp_786_;
}
}
}
else
{
lean_object* v_snd_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_839_; 
v_snd_804_ = lean_ctor_get(v_b_780_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_b_780_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_b_780_, 0);
lean_dec(v_unused_840_);
v___x_806_ = v_b_780_;
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snd_804_);
lean_dec(v_b_780_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc(v_a_779_);
lean_inc(v_fst_793_);
v___x_808_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_793_, v_snd_804_, v_a_779_, v_args_777_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
v___x_809_ = lean_whnf(v___x_808_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
if (lean_obj_tag(v_a_810_) == 7)
{
lean_object* v_body_811_; lean_object* v___x_813_; 
lean_dec(v_snd_804_);
lean_dec(v_fst_793_);
v_body_811_ = lean_ctor_get(v_a_810_, 2);
lean_inc_ref(v_body_811_);
lean_dec_ref_known(v_a_810_, 3);
lean_inc(v_a_779_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v_a_779_);
lean_ctor_set(v___x_806_, 0, v_body_811_);
v___x_813_ = v___x_806_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_body_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_779_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v_a_787_ = v___x_813_;
goto v___jp_786_;
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_a_810_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_a_779_, v___x_816_);
lean_inc_ref(v_f_778_);
v___x_818_ = l_Lean_mkAppRange(v_f_778_, v___x_815_, v___x_817_, v_args_777_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_818_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_821_; 
lean_dec_ref_known(v___x_819_, 1);
if (v_isShared_807_ == 0)
{
v___x_821_ = v___x_806_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_fst_793_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_snd_804_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v_a_787_ = v___x_821_;
goto v___jp_786_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_del_object(v___x_806_);
lean_dec(v_snd_804_);
lean_dec(v_fst_793_);
lean_dec(v_a_779_);
lean_dec_ref(v_f_778_);
v_a_823_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_819_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_806_);
lean_dec(v_snd_804_);
lean_dec(v_fst_793_);
lean_dec(v_a_779_);
lean_dec_ref(v_f_778_);
v_a_831_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_809_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_809_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_add(v_a_779_, v___x_788_);
lean_dec(v_a_779_);
v_a_779_ = v___x_789_;
v_b_780_ = v_a_787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_841_, lean_object* v_args_842_, lean_object* v_f_843_, lean_object* v_a_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_841_, v_args_842_, v_f_843_, v_a_844_, v_b_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_args_842_);
lean_dec(v_upperBound_841_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_852_, lean_object* v_args_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_859_; 
lean_inc(v_a_857_);
lean_inc_ref(v_a_856_);
lean_inc(v_a_855_);
lean_inc_ref(v_a_854_);
lean_inc_ref(v_f_852_);
v___x_859_ = lean_infer_type(v_f_852_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = lean_array_get_size(v_args_853_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_a_860_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_861_, v_args_853_, v_f_852_, v___x_862_, v___x_863_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_875_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_875_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v_fst_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_a_865_, 1);
lean_inc(v_snd_870_);
lean_dec(v_a_865_);
v___x_871_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_869_, v_snd_870_, v___x_861_, v_args_853_);
lean_dec(v_snd_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_864_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_864_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_dec_ref(v_f_852_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_884_, lean_object* v_args_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_884_, v_args_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec_ref(v_args_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_892_, lean_object* v_args_893_, lean_object* v_f_894_, lean_object* v_inst_895_, lean_object* v_R_896_, lean_object* v_a_897_, lean_object* v_b_898_, lean_object* v_c_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_892_, v_args_893_, v_f_894_, v_a_897_, v_b_898_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_906_, lean_object* v_args_907_, lean_object* v_f_908_, lean_object* v_inst_909_, lean_object* v_R_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_c_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_906_, v_args_907_, v_f_908_, v_inst_909_, v_R_910_, v_a_911_, v_b_912_, v_c_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_args_907_);
lean_dec(v_upperBound_906_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_923_, lean_object* v_us_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_931_ = l_Lean_mkConst(v_constName_923_, v_us_924_);
v___x_932_ = l_Lean_MessageData_ofExpr(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_933_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_935_, lean_object* v_us_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_935_, v_us_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_943_, lean_object* v_constName_944_, lean_object* v_us_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_944_, v_us_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_952_, lean_object* v_constName_953_, lean_object* v_us_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_952_, v_constName_953_, v_us_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_toCold_968_; lean_object* v_currRecDepth_969_; lean_object* v_ref_970_; uint8_t v_diag_971_; uint8_t v_suppressElabErrors_972_; lean_object* v_ref_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_toCold_968_ = lean_ctor_get(v___y_965_, 0);
v_currRecDepth_969_ = lean_ctor_get(v___y_965_, 1);
v_ref_970_ = lean_ctor_get(v___y_965_, 2);
v_diag_971_ = lean_ctor_get_uint8(v___y_965_, sizeof(void*)*3);
v_suppressElabErrors_972_ = lean_ctor_get_uint8(v___y_965_, sizeof(void*)*3 + 1);
v_ref_973_ = l_Lean_replaceRef(v_ref_961_, v_ref_970_);
lean_inc(v_currRecDepth_969_);
lean_inc_ref(v_toCold_968_);
v___x_974_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_974_, 0, v_toCold_968_);
lean_ctor_set(v___x_974_, 1, v_currRecDepth_969_);
lean_ctor_set(v___x_974_, 2, v_ref_973_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3, v_diag_971_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*3 + 1, v_suppressElabErrors_972_);
v___x_975_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_962_, v___y_963_, v___y_964_, v___x_974_, v___y_966_);
lean_dec_ref_known(v___x_974_, 3);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_976_, lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_976_, v_msg_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v_ref_976_);
return v_res_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
lean_ctor_set(v___x_989_, 4, v___x_987_);
lean_ctor_set(v___x_989_, 5, v___x_987_);
lean_ctor_set(v___x_989_, 6, v___x_987_);
lean_ctor_set(v___x_989_, 7, v___x_987_);
lean_ctor_set(v___x_989_, 8, v___x_987_);
lean_ctor_set(v___x_989_, 9, v___x_987_);
lean_ctor_set(v___x_989_, 10, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_unsigned_to_nat(32u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_993_ = ((size_t)5ULL);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_unsigned_to_nat(32u);
v___x_996_ = lean_mk_empty_array_with_capacity(v___x_995_);
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_998_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
lean_ctor_set(v___x_998_, 2, v___x_994_);
lean_ctor_set(v___x_998_, 3, v___x_994_);
lean_ctor_set_usize(v___x_998_, 4, v___x_993_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = lean_box(1);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_999_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1024_, lean_object* v_declHint_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_env_1029_; uint8_t v___x_1030_; 
v___x_1028_ = lean_st_ref_get(v___y_1026_);
v_env_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_env_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = l_Lean_Name_isAnonymous(v_declHint_1025_);
if (v___x_1030_ == 0)
{
uint8_t v_isExporting_1031_; 
v_isExporting_1031_ = lean_ctor_get_uint8(v_env_1029_, sizeof(void*)*8);
if (v_isExporting_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref(v_env_1029_);
lean_dec(v_declHint_1025_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_msg_1024_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
lean_inc_ref(v_env_1029_);
v___x_1033_ = l_Lean_Environment_setExporting(v_env_1029_, v___x_1030_);
lean_inc(v_declHint_1025_);
lean_inc_ref(v___x_1033_);
v___x_1034_ = l_Lean_Environment_contains(v___x_1033_, v_declHint_1025_, v_isExporting_1031_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v___x_1033_);
lean_dec_ref(v_env_1029_);
lean_dec(v_declHint_1025_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_1024_);
return v___x_1035_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_c_1041_; lean_object* v___x_1042_; 
v___x_1036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1038_ = l_Lean_Options_empty;
v___x_1039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1036_);
lean_ctor_set(v___x_1039_, 2, v___x_1037_);
lean_ctor_set(v___x_1039_, 3, v___x_1038_);
lean_inc(v_declHint_1025_);
v___x_1040_ = l_Lean_MessageData_ofConstName(v_declHint_1025_, v___x_1030_);
v_c_1041_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1041_, 0, v___x_1039_);
lean_ctor_set(v_c_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1029_, v_declHint_1025_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_env_1029_);
lean_dec(v_declHint_1025_);
v___x_1043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_c_1041_);
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_MessageData_note(v___x_1046_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_msg_1024_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1085_; 
v_val_1050_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1052_ = v___x_1042_;
v_isShared_1053_ = v_isSharedCheck_1085_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v___x_1042_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1085_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_mod_1057_; uint8_t v___x_1058_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Lean_Environment_header(v_env_1029_);
lean_dec_ref(v_env_1029_);
v___x_1056_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1055_);
v_mod_1057_ = lean_array_get(v___x_1054_, v___x_1056_, v_val_1050_);
lean_dec(v_val_1050_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = l_Lean_isPrivateName(v_declHint_1025_);
lean_dec(v_declHint_1025_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_c_1041_);
v___x_1061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_MessageData_ofName(v_mod_1057_);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_MessageData_note(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_msg_1024_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1068_);
v___x_1070_ = v___x_1052_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_c_1041_);
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_MessageData_ofName(v_mod_1057_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_MessageData_note(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_msg_1024_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1081_);
v___x_1083_ = v___x_1052_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1086_; 
lean_dec_ref(v_env_1029_);
lean_dec(v_declHint_1025_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_msg_1024_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1087_, lean_object* v_declHint_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1087_, v_declHint_1088_, v___y_1089_);
lean_dec(v___y_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1092_, lean_object* v_declHint_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v___x_1099_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1092_, v_declHint_1093_, v___y_1097_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = l_Lean_unknownIdentifierMessageTag;
v___x_1105_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1110_, v_declHint_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1118_, lean_object* v_msg_1119_, lean_object* v_declHint_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v_a_1127_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1119_, v_declHint_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1118_, v_a_1127_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1129_, lean_object* v_msg_1130_, lean_object* v_declHint_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1129_, v_msg_1130_, v_declHint_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_ref_1129_);
return v_res_1137_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1144_, lean_object* v_constName_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1151_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1152_ = 0;
lean_inc(v_constName_1145_);
v___x_1153_ = l_Lean_MessageData_ofConstName(v_constName_1145_, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1151_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1144_, v___x_1156_, v_constName_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1158_, lean_object* v_constName_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1158_, v_constName_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v_ref_1158_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_ref_1172_; lean_object* v___x_1173_; 
v_ref_1172_ = lean_ctor_get(v___y_1169_, 2);
v___x_1173_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1172_, v_constName_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_env_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1187_ = lean_st_ref_get(v___y_1185_);
v_env_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_ref(v_env_1188_);
lean_dec(v___x_1187_);
v___x_1189_ = 0;
lean_inc(v_constName_1181_);
v___x_1190_ = l_Lean_Environment_findConstVal_x3f(v_env_1188_, v_constName_1181_, v___x_1189_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_constName_1181_);
v_val_1192_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1190_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_dec(v___x_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 0);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_val_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1207_, lean_object* v_us_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; 
lean_inc(v_c_1207_);
v___x_1214_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1207_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v_levelParams_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v_levelParams_1216_ = lean_ctor_get(v_a_1215_, 1);
v___x_1217_ = l_List_lengthTR___redArg(v_levelParams_1216_);
v___x_1218_ = l_List_lengthTR___redArg(v_us_1208_);
v___x_1219_ = lean_nat_dec_eq(v___x_1217_, v___x_1218_);
lean_dec(v___x_1218_);
lean_dec(v___x_1217_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
lean_dec(v_a_1215_);
v___x_1220_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1207_, v_us_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; 
lean_dec(v_c_1207_);
v___x_1221_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1215_, v_us_1208_, v_a_1212_);
return v___x_1221_;
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_us_1208_);
lean_dec(v_c_1207_);
v_a_1222_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1214_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1214_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1230_, lean_object* v_us_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1230_, v_us_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1238_, lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_constName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1246_, v_constName_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1254_, lean_object* v_ref_1255_, lean_object* v_constName_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1255_, v_constName_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_ref_1264_, lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1263_, v_ref_1264_, v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v_ref_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_msg_1274_, lean_object* v_declHint_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1273_, v_msg_1274_, v_declHint_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v_declHint_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1282_, v_ref_1283_, v_msg_1284_, v_declHint_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v_ref_1283_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1292_, lean_object* v_declHint_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1292_, v_declHint_1293_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1300_, lean_object* v_declHint_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1300_, v_declHint_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1308_, lean_object* v_ref_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1309_, v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_ref_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1317_, v_ref_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v_ref_1318_);
return v_res_1325_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1332_, lean_object* v_idx_1333_, lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_00_u03b1_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1343_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1344_ = l_Lean_mkProj(v_structName_1332_, v_idx_1333_, v_e_1334_);
v___x_1345_ = l_Lean_indentExpr(v___x_1344_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_indentExpr(v_a_1335_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1350_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1352_, lean_object* v_idx_1353_, lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v_00_u03b1_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1352_, v_idx_1353_, v_e_1354_, v_a_1355_, v_00_u03b1_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_env_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = 0;
lean_inc(v_constName_1364_);
v___x_1373_ = l_Lean_Environment_find_x3f(v_env_1371_, v_constName_1364_, v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1374_;
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_constName_1364_);
v_val_1375_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1373_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_val_1375_);
lean_dec(v___x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 0);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_val_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1390_, lean_object* v_structName_1391_, lean_object* v_e_1392_, lean_object* v_idx_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_a_1403_; uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_lt(v_a_1395_, v_upperBound_1390_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_idx_1393_);
lean_dec_ref(v_e_1392_);
lean_dec(v_structName_1391_);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_b_1396_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; 
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___x_1409_ = lean_whnf(v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
if (lean_obj_tag(v_a_1410_) == 7)
{
lean_object* v_body_1411_; uint8_t v___x_1412_; 
v_body_1411_ = lean_ctor_get(v_a_1410_, 2);
lean_inc_ref(v_body_1411_);
lean_dec_ref_known(v_a_1410_, 3);
v___x_1412_ = l_Lean_Expr_hasLooseBVars(v_body_1411_);
if (v___x_1412_ == 0)
{
v_a_1403_ = v_body_1411_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_inc_ref(v_e_1392_);
lean_inc(v_a_1395_);
lean_inc(v_structName_1391_);
v___x_1413_ = l_Lean_mkProj(v_structName_1391_, v_a_1395_, v_e_1392_);
v___x_1414_ = lean_expr_instantiate1(v_body_1411_, v___x_1413_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v_body_1411_);
v_a_1403_ = v___x_1414_;
goto v___jp_1402_;
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1415_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1392_);
lean_inc(v_idx_1393_);
lean_inc(v_structName_1391_);
v___x_1416_ = l_Lean_mkProj(v_structName_1391_, v_idx_1393_, v_e_1392_);
v___x_1417_ = l_Lean_indentExpr(v___x_1416_);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1415_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
lean_inc_ref(v_a_1394_);
v___x_1421_ = l_Lean_indentExpr(v_a_1394_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1422_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_dec_ref_known(v___x_1423_, 1);
v_a_1403_ = v_a_1410_;
goto v___jp_1402_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_a_1410_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_idx_1393_);
lean_dec_ref(v_e_1392_);
lean_dec(v_structName_1391_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_idx_1393_);
lean_dec_ref(v_e_1392_);
lean_dec(v_structName_1391_);
return v___x_1409_;
}
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_add(v_a_1395_, v___x_1404_);
lean_dec(v_a_1395_);
v_a_1395_ = v___x_1405_;
v_b_1396_ = v_a_1403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1432_, lean_object* v_structName_1433_, lean_object* v_e_1434_, lean_object* v_idx_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1432_, v_structName_1433_, v_e_1434_, v_idx_1435_, v_a_1436_, v_a_1437_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_upperBound_1432_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1445_, lean_object* v_structName_1446_, lean_object* v_e_1447_, lean_object* v_idx_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_a_1458_; uint8_t v___x_1462_; 
v___x_1462_ = lean_nat_dec_lt(v_a_1450_, v_upperBound_1445_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_idx_1448_);
lean_dec_ref(v_e_1447_);
lean_dec(v_structName_1446_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1451_);
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; 
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
v___x_1464_ = lean_whnf(v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
if (lean_obj_tag(v_a_1465_) == 7)
{
lean_object* v_body_1466_; uint8_t v___x_1467_; 
v_body_1466_ = lean_ctor_get(v_a_1465_, 2);
lean_inc_ref(v_body_1466_);
lean_dec_ref_known(v_a_1465_, 3);
v___x_1467_ = l_Lean_Expr_hasLooseBVars(v_body_1466_);
if (v___x_1467_ == 0)
{
v_a_1458_ = v_body_1466_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc_ref(v_e_1447_);
lean_inc(v_a_1450_);
lean_inc(v_structName_1446_);
v___x_1468_ = l_Lean_mkProj(v_structName_1446_, v_a_1450_, v_e_1447_);
v___x_1469_ = lean_expr_instantiate1(v_body_1466_, v___x_1468_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_body_1466_);
v_a_1458_ = v___x_1469_;
goto v___jp_1457_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1447_);
lean_inc(v_idx_1448_);
lean_inc(v_structName_1446_);
v___x_1471_ = l_Lean_mkProj(v_structName_1446_, v_idx_1448_, v_e_1447_);
v___x_1472_ = l_Lean_indentExpr(v___x_1471_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
lean_inc_ref(v_a_1449_);
v___x_1476_ = l_Lean_indentExpr(v_a_1449_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1477_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec_ref_known(v___x_1478_, 1);
v_a_1458_ = v_a_1465_;
goto v___jp_1457_;
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1465_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_idx_1448_);
lean_dec_ref(v_e_1447_);
lean_dec(v_structName_1446_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_idx_1448_);
lean_dec_ref(v_e_1447_);
lean_dec(v_structName_1446_);
return v___x_1464_;
}
}
v___jp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_a_1450_, v___x_1459_);
lean_dec(v_a_1450_);
v___x_1461_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1445_, v_structName_1446_, v_e_1447_, v_idx_1448_, v_a_1449_, v___x_1460_, v_a_1458_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1487_, lean_object* v_structName_1488_, lean_object* v_e_1489_, lean_object* v_idx_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1487_, v_structName_1488_, v_e_1489_, v_idx_1490_, v_a_1491_, v_a_1492_, v_b_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_upperBound_1487_);
return v_res_1499_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1500_; lean_object* v_dummy_1501_; 
v___x_1500_ = lean_box(0);
v_dummy_1501_ = l_Lean_Expr_sort___override(v___x_1500_);
return v_dummy_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1502_, lean_object* v_idx_1503_, lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; 
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
lean_inc_ref(v_e_1504_);
v___x_1510_ = lean_infer_type(v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
v___x_1512_ = lean_whnf(v_a_1511_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l_Lean_Expr_getAppFn(v_a_1513_);
if (lean_obj_tag(v___x_1514_) == 4)
{
lean_object* v_declName_1515_; lean_object* v_us_1516_; lean_object* v___x_1517_; lean_object* v_env_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; 
v_declName_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_declName_1515_);
v_us_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc(v_us_1516_);
lean_dec_ref_known(v___x_1514_, 2);
v___x_1517_ = lean_st_ref_get(v_a_1508_);
v_env_1521_ = lean_ctor_get(v___x_1517_, 0);
lean_inc_ref(v_env_1521_);
lean_dec(v___x_1517_);
v___x_1522_ = 0;
v___x_1523_ = l_Lean_Environment_find_x3f(v_env_1521_, v_declName_1515_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_us_1516_);
v___x_1524_ = lean_box(0);
v___x_1525_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1524_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1523_, 1);
if (lean_obj_tag(v_val_1526_) == 5)
{
lean_object* v_val_1527_; lean_object* v_ctors_1528_; 
v_val_1527_ = lean_ctor_get(v_val_1526_, 0);
lean_inc_ref(v_val_1527_);
lean_dec_ref_known(v_val_1526_, 1);
v_ctors_1528_ = lean_ctor_get(v_val_1527_, 4);
lean_inc(v_ctors_1528_);
if (lean_obj_tag(v_ctors_1528_) == 1)
{
lean_object* v_tail_1529_; 
v_tail_1529_ = lean_ctor_get(v_ctors_1528_, 1);
if (lean_obj_tag(v_tail_1529_) == 0)
{
lean_object* v_toConstantVal_1530_; lean_object* v_numParams_1531_; lean_object* v_numIndices_1532_; lean_object* v_head_1533_; lean_object* v___x_1534_; 
v_toConstantVal_1530_ = lean_ctor_get(v_val_1527_, 0);
lean_inc_ref(v_toConstantVal_1530_);
v_numParams_1531_ = lean_ctor_get(v_val_1527_, 1);
lean_inc(v_numParams_1531_);
v_numIndices_1532_ = lean_ctor_get(v_val_1527_, 2);
lean_inc(v_numIndices_1532_);
lean_dec_ref(v_val_1527_);
v_head_1533_ = lean_ctor_get(v_ctors_1528_, 0);
lean_inc(v_head_1533_);
lean_dec_ref_known(v_ctors_1528_, 2);
v___x_1534_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1533_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
if (lean_obj_tag(v_a_1535_) == 6)
{
lean_object* v_val_1536_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_name_1576_; uint8_t v___x_1577_; 
v_val_1536_ = lean_ctor_get(v_a_1535_, 0);
lean_inc_ref(v_val_1536_);
lean_dec_ref_known(v_a_1535_, 1);
v_name_1576_ = lean_ctor_get(v_toConstantVal_1530_, 0);
lean_inc(v_name_1576_);
lean_dec_ref(v_toConstantVal_1530_);
v___x_1577_ = lean_name_eq(v_name_1576_, v_structName_1502_);
lean_dec(v_name_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_val_1536_);
lean_dec(v_numIndices_1532_);
lean_dec(v_numParams_1531_);
lean_dec(v_us_1516_);
v___x_1578_ = lean_box(0);
v___x_1579_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1578_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
v___y_1538_ = v_a_1505_;
v___y_1539_ = v_a_1506_;
v___y_1540_ = v_a_1507_;
v___y_1541_ = v_a_1508_;
goto v___jp_1537_;
}
v___jp_1537_:
{
lean_object* v_dummy_1542_; lean_object* v_nargs_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_dummy_1542_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1543_ = l_Lean_Expr_getAppNumArgs(v_a_1513_);
lean_inc(v_nargs_1543_);
v___x_1544_ = lean_mk_array(v_nargs_1543_, v_dummy_1542_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_sub(v_nargs_1543_, v___x_1545_);
lean_dec(v_nargs_1543_);
lean_inc(v_a_1513_);
v___x_1547_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1513_, v___x_1544_, v___x_1546_);
v___x_1548_ = lean_nat_add(v_numParams_1531_, v_numIndices_1532_);
lean_dec(v_numIndices_1532_);
v___x_1549_ = lean_array_get_size(v___x_1547_);
v___x_1550_ = lean_nat_dec_eq(v___x_1548_, v___x_1549_);
lean_dec(v___x_1548_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_val_1536_);
lean_dec(v_numParams_1531_);
lean_dec(v_us_1516_);
v___x_1551_ = lean_box(0);
v___x_1552_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1551_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1552_;
}
else
{
lean_object* v_toConstantVal_1553_; lean_object* v_name_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_toConstantVal_1553_ = lean_ctor_get(v_val_1536_, 0);
lean_inc_ref(v_toConstantVal_1553_);
lean_dec_ref(v_val_1536_);
v_name_1554_ = lean_ctor_get(v_toConstantVal_1553_, 0);
lean_inc(v_name_1554_);
lean_dec_ref(v_toConstantVal_1553_);
v___x_1555_ = l_Lean_mkConst(v_name_1554_, v_us_1516_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = l_Array_toSubarray___redArg(v___x_1547_, v___x_1556_, v_numParams_1531_);
v___x_1558_ = l_Subarray_copy___redArg(v___x_1557_);
v___x_1559_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1555_, v___x_1558_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec_ref(v___x_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
lean_inc(v_a_1513_);
lean_inc_ref(v_e_1504_);
lean_inc(v_structName_1502_);
lean_inc(v_idx_1503_);
v___x_1561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1503_, v_structName_1502_, v_e_1504_, v_idx_1503_, v_a_1513_, v___x_1556_, v_a_1560_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v___x_1563_ = lean_whnf(v_a_1562_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1575_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
if (lean_obj_tag(v_a_1564_) == 7)
{
lean_object* v_binderType_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
v_binderType_1568_ = lean_ctor_get(v_a_1564_, 1);
lean_inc_ref(v_binderType_1568_);
lean_dec_ref_known(v_a_1564_, 3);
v___x_1569_ = lean_expr_consume_type_annotations(v_binderType_1568_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1566_);
lean_dec(v_a_1564_);
v___x_1573_ = lean_box(0);
v___x_1574_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1573_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1574_;
}
}
}
else
{
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
return v___x_1563_;
}
}
else
{
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
return v___x_1561_;
}
}
else
{
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
return v___x_1559_;
}
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v_a_1535_);
lean_dec(v_numIndices_1532_);
lean_dec(v_numParams_1531_);
lean_dec_ref(v_toConstantVal_1530_);
lean_dec(v_us_1516_);
v___x_1588_ = lean_box(0);
v___x_1589_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1588_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1589_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_numIndices_1532_);
lean_dec(v_numParams_1531_);
lean_dec_ref(v_toConstantVal_1530_);
lean_dec(v_us_1516_);
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
v_a_1590_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1534_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1534_);
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
}
else
{
lean_dec_ref_known(v_ctors_1528_, 2);
lean_dec_ref(v_val_1527_);
lean_dec(v_us_1516_);
goto v___jp_1518_;
}
}
else
{
lean_dec(v_ctors_1528_);
lean_dec_ref(v_val_1527_);
lean_dec(v_us_1516_);
goto v___jp_1518_;
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_val_1526_);
lean_dec(v_us_1516_);
v___x_1598_ = lean_box(0);
v___x_1599_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1598_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1599_;
}
}
v___jp_1518_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1519_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1520_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v___x_1514_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1513_, lean_box(0), v___x_1600_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1601_;
}
}
else
{
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
return v___x_1512_;
}
}
else
{
lean_dec_ref(v_e_1504_);
lean_dec(v_idx_1503_);
lean_dec(v_structName_1502_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1602_, lean_object* v_idx_1603_, lean_object* v_e_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1602_, v_idx_1603_, v_e_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1611_, lean_object* v_structName_1612_, lean_object* v_e_1613_, lean_object* v_idx_1614_, lean_object* v_a_1615_, lean_object* v_inst_1616_, lean_object* v_R_1617_, lean_object* v_a_1618_, lean_object* v_b_1619_, lean_object* v_c_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1611_, v_structName_1612_, v_e_1613_, v_idx_1614_, v_a_1615_, v_a_1618_, v_b_1619_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1627_, lean_object* v_structName_1628_, lean_object* v_e_1629_, lean_object* v_idx_1630_, lean_object* v_a_1631_, lean_object* v_inst_1632_, lean_object* v_R_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_, lean_object* v_c_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1627_, v_structName_1628_, v_e_1629_, v_idx_1630_, v_a_1631_, v_inst_1632_, v_R_1633_, v_a_1634_, v_b_1635_, v_c_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v_upperBound_1627_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1643_, lean_object* v_structName_1644_, lean_object* v_e_1645_, lean_object* v_idx_1646_, lean_object* v_a_1647_, lean_object* v_inst_1648_, lean_object* v_R_1649_, lean_object* v_a_1650_, lean_object* v_b_1651_, lean_object* v_c_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1643_, v_structName_1644_, v_e_1645_, v_idx_1646_, v_a_1647_, v_a_1650_, v_b_1651_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1659_, lean_object* v_structName_1660_, lean_object* v_e_1661_, lean_object* v_idx_1662_, lean_object* v_a_1663_, lean_object* v_inst_1664_, lean_object* v_R_1665_, lean_object* v_a_1666_, lean_object* v_b_1667_, lean_object* v_c_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1659_, v_structName_1660_, v_e_1661_, v_idx_1662_, v_a_1663_, v_inst_1664_, v_R_1665_, v_a_1666_, v_b_1667_, v_c_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v_upperBound_1659_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1685_ = l_Lean_indentExpr(v_type_1678_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1686_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1695_, lean_object* v_type_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_type_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1703_, v_type_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_ks_1715_; lean_object* v_vs_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1740_; 
v_ks_1715_ = lean_ctor_get(v_x_1711_, 0);
v_vs_1716_ = lean_ctor_get(v_x_1711_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1718_ = v_x_1711_;
v_isShared_1719_ = v_isSharedCheck_1740_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_vs_1716_);
lean_inc(v_ks_1715_);
lean_dec(v_x_1711_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1740_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = lean_array_get_size(v_ks_1715_);
v___x_1721_ = lean_nat_dec_lt(v_x_1712_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
lean_dec(v_x_1712_);
v___x_1722_ = lean_array_push(v_ks_1715_, v_x_1713_);
v___x_1723_ = lean_array_push(v_vs_1716_, v_x_1714_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v___x_1723_);
lean_ctor_set(v___x_1718_, 0, v___x_1722_);
v___x_1725_ = v___x_1718_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
else
{
lean_object* v_k_x27_1727_; uint8_t v___x_1728_; 
v_k_x27_1727_ = lean_array_fget_borrowed(v_ks_1715_, v_x_1712_);
v___x_1728_ = l_Lean_instBEqMVarId_beq(v_x_1713_, v_k_x27_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1730_; 
if (v_isShared_1719_ == 0)
{
v___x_1730_ = v___x_1718_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_ks_1715_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_vs_1716_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_add(v_x_1712_, v___x_1731_);
lean_dec(v_x_1712_);
v_x_1711_ = v___x_1730_;
v_x_1712_ = v___x_1732_;
goto _start;
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = lean_array_fset(v_ks_1715_, v_x_1712_, v_x_1713_);
v___x_1736_ = lean_array_fset(v_vs_1716_, v_x_1712_, v_x_1714_);
lean_dec(v_x_1712_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v___x_1736_);
lean_ctor_set(v___x_1718_, 0, v___x_1735_);
v___x_1738_ = v___x_1718_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1741_, lean_object* v_k_1742_, lean_object* v_v_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1741_, v___x_1744_, v_k_1742_, v_v_1743_);
return v___x_1745_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1747_, size_t v_x_1748_, size_t v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v_es_1752_; size_t v___x_1753_; size_t v___x_1754_; lean_object* v_j_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_es_1752_ = lean_ctor_get(v_x_1747_, 0);
v___x_1753_ = ((size_t)31ULL);
v___x_1754_ = lean_usize_land(v_x_1748_, v___x_1753_);
v_j_1755_ = lean_usize_to_nat(v___x_1754_);
v___x_1756_ = lean_array_get_size(v_es_1752_);
v___x_1757_ = lean_nat_dec_lt(v_j_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec(v_j_1755_);
lean_dec(v_x_1751_);
lean_dec(v_x_1750_);
return v_x_1747_;
}
else
{
lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1796_; 
lean_inc_ref(v_es_1752_);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_x_1747_, 0);
lean_dec(v_unused_1797_);
v___x_1759_ = v_x_1747_;
v_isShared_1760_ = v_isSharedCheck_1796_;
goto v_resetjp_1758_;
}
else
{
lean_dec(v_x_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1796_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_v_1761_; lean_object* v___x_1762_; lean_object* v_xs_x27_1763_; lean_object* v___y_1765_; 
v_v_1761_ = lean_array_fget(v_es_1752_, v_j_1755_);
v___x_1762_ = lean_box(0);
v_xs_x27_1763_ = lean_array_fset(v_es_1752_, v_j_1755_, v___x_1762_);
switch(lean_obj_tag(v_v_1761_))
{
case 0:
{
lean_object* v_key_1770_; lean_object* v_val_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
v_key_1770_ = lean_ctor_get(v_v_1761_, 0);
v_val_1771_ = lean_ctor_get(v_v_1761_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_v_1761_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1773_ = v_v_1761_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_val_1771_);
lean_inc(v_key_1770_);
lean_dec(v_v_1761_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
uint8_t v___x_1775_; 
v___x_1775_ = l_Lean_instBEqMVarId_beq(v_x_1750_, v_key_1770_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1773_);
v___x_1776_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1770_, v_val_1771_, v_x_1750_, v_x_1751_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
v___y_1765_ = v___x_1777_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1779_; 
lean_dec(v_val_1771_);
lean_dec(v_key_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v_x_1751_);
lean_ctor_set(v___x_1773_, 0, v_x_1750_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_x_1750_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_x_1751_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v___y_1765_ = v___x_1779_;
goto v___jp_1764_;
}
}
}
}
case 1:
{
lean_object* v_node_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1794_; 
v_node_1782_ = lean_ctor_get(v_v_1761_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_v_1761_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1784_ = v_v_1761_;
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_node_1782_);
lean_dec(v_v_1761_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1794_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
size_t v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; size_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1786_ = ((size_t)5ULL);
v___x_1787_ = lean_usize_shift_right(v_x_1748_, v___x_1786_);
v___x_1788_ = ((size_t)1ULL);
v___x_1789_ = lean_usize_add(v_x_1749_, v___x_1788_);
v___x_1790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1782_, v___x_1787_, v___x_1789_, v_x_1750_, v_x_1751_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1790_);
v___x_1792_ = v___x_1784_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1765_ = v___x_1792_;
goto v___jp_1764_;
}
}
}
default: 
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_x_1750_);
lean_ctor_set(v___x_1795_, 1, v_x_1751_);
v___y_1765_ = v___x_1795_;
goto v___jp_1764_;
}
}
v___jp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_array_fset(v_xs_x27_1763_, v_j_1755_, v___y_1765_);
lean_dec(v_j_1755_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1766_);
v___x_1768_ = v___x_1759_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v_ks_1798_; lean_object* v_vs_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1817_; 
v_ks_1798_ = lean_ctor_get(v_x_1747_, 0);
v_vs_1799_ = lean_ctor_get(v_x_1747_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1801_ = v_x_1747_;
v_isShared_1802_ = v_isSharedCheck_1817_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_vs_1799_);
lean_inc(v_ks_1798_);
lean_dec(v_x_1747_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1817_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_ks_1798_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_vs_1799_);
v___x_1804_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v_newNode_1805_; size_t v___x_1806_; uint8_t v___x_1807_; 
v_newNode_1805_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1804_, v_x_1750_, v_x_1751_);
v___x_1806_ = ((size_t)7ULL);
v___x_1807_ = lean_usize_dec_le(v___x_1806_, v_x_1749_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1805_);
v___x_1809_ = lean_unsigned_to_nat(4u);
v___x_1810_ = lean_nat_dec_lt(v___x_1808_, v___x_1809_);
lean_dec(v___x_1808_);
if (v___x_1810_ == 0)
{
lean_object* v_ks_1811_; lean_object* v_vs_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_ks_1811_ = lean_ctor_get(v_newNode_1805_, 0);
lean_inc_ref(v_ks_1811_);
v_vs_1812_ = lean_ctor_get(v_newNode_1805_, 1);
lean_inc_ref(v_vs_1812_);
lean_dec_ref(v_newNode_1805_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1815_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1749_, v_ks_1811_, v_vs_1812_, v___x_1813_, v___x_1814_);
lean_dec_ref(v_vs_1812_);
lean_dec_ref(v_ks_1811_);
return v___x_1815_;
}
else
{
return v_newNode_1805_;
}
}
else
{
return v_newNode_1805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1818_, lean_object* v_keys_1819_, lean_object* v_vals_1820_, lean_object* v_i_1821_, lean_object* v_entries_1822_){
_start:
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_array_get_size(v_keys_1819_);
v___x_1824_ = lean_nat_dec_lt(v_i_1821_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec(v_i_1821_);
return v_entries_1822_;
}
else
{
lean_object* v_k_1825_; lean_object* v_v_1826_; uint64_t v___x_1827_; size_t v_h_1828_; size_t v___x_1829_; lean_object* v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; size_t v___x_1833_; size_t v_h_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_k_1825_ = lean_array_fget_borrowed(v_keys_1819_, v_i_1821_);
v_v_1826_ = lean_array_fget_borrowed(v_vals_1820_, v_i_1821_);
v___x_1827_ = l_Lean_instHashableMVarId_hash(v_k_1825_);
v_h_1828_ = lean_uint64_to_usize(v___x_1827_);
v___x_1829_ = ((size_t)5ULL);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_sub(v_depth_1818_, v___x_1831_);
v___x_1833_ = lean_usize_mul(v___x_1829_, v___x_1832_);
v_h_1834_ = lean_usize_shift_right(v_h_1828_, v___x_1833_);
v___x_1835_ = lean_nat_add(v_i_1821_, v___x_1830_);
lean_dec(v_i_1821_);
lean_inc(v_v_1826_);
lean_inc(v_k_1825_);
v___x_1836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1822_, v_h_1834_, v_depth_1818_, v_k_1825_, v_v_1826_);
v_i_1821_ = v___x_1835_;
v_entries_1822_ = v___x_1836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1838_, lean_object* v_keys_1839_, lean_object* v_vals_1840_, lean_object* v_i_1841_, lean_object* v_entries_1842_){
_start:
{
size_t v_depth_boxed_1843_; lean_object* v_res_1844_; 
v_depth_boxed_1843_ = lean_unbox_usize(v_depth_1838_);
lean_dec(v_depth_1838_);
v_res_1844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1843_, v_keys_1839_, v_vals_1840_, v_i_1841_, v_entries_1842_);
lean_dec_ref(v_vals_1840_);
lean_dec_ref(v_keys_1839_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
size_t v_x_1146__boxed_1850_; size_t v_x_1147__boxed_1851_; lean_object* v_res_1852_; 
v_x_1146__boxed_1850_ = lean_unbox_usize(v_x_1846_);
lean_dec(v_x_1846_);
v_x_1147__boxed_1851_ = lean_unbox_usize(v_x_1847_);
lean_dec(v_x_1847_);
v_res_1852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1845_, v_x_1146__boxed_1850_, v_x_1147__boxed_1851_, v_x_1848_, v_x_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
uint64_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = l_Lean_instHashableMVarId_hash(v_x_1854_);
v___x_1857_ = lean_uint64_to_usize(v___x_1856_);
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1853_, v___x_1857_, v___x_1858_, v_x_1854_, v_x_1855_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1860_, lean_object* v_val_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v_mctx_1865_; lean_object* v_cache_1866_; lean_object* v_zetaDeltaFVarIds_1867_; lean_object* v_postponed_1868_; lean_object* v_diag_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1898_; 
v___x_1864_ = lean_st_ref_take(v___y_1862_);
v_mctx_1865_ = lean_ctor_get(v___x_1864_, 0);
v_cache_1866_ = lean_ctor_get(v___x_1864_, 1);
v_zetaDeltaFVarIds_1867_ = lean_ctor_get(v___x_1864_, 2);
v_postponed_1868_ = lean_ctor_get(v___x_1864_, 3);
v_diag_1869_ = lean_ctor_get(v___x_1864_, 4);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1871_ = v___x_1864_;
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_diag_1869_);
lean_inc(v_postponed_1868_);
lean_inc(v_zetaDeltaFVarIds_1867_);
lean_inc(v_cache_1866_);
lean_inc(v_mctx_1865_);
lean_dec(v___x_1864_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1898_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_depth_1873_; lean_object* v_levelAssignDepth_1874_; lean_object* v_lmvarCounter_1875_; lean_object* v_mvarCounter_1876_; lean_object* v_lDecls_1877_; lean_object* v_decls_1878_; lean_object* v_userNames_1879_; lean_object* v_lAssignment_1880_; lean_object* v_eAssignment_1881_; lean_object* v_dAssignment_1882_; lean_object* v_instanceTypedMVars_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1897_; 
v_depth_1873_ = lean_ctor_get(v_mctx_1865_, 0);
v_levelAssignDepth_1874_ = lean_ctor_get(v_mctx_1865_, 1);
v_lmvarCounter_1875_ = lean_ctor_get(v_mctx_1865_, 2);
v_mvarCounter_1876_ = lean_ctor_get(v_mctx_1865_, 3);
v_lDecls_1877_ = lean_ctor_get(v_mctx_1865_, 4);
v_decls_1878_ = lean_ctor_get(v_mctx_1865_, 5);
v_userNames_1879_ = lean_ctor_get(v_mctx_1865_, 6);
v_lAssignment_1880_ = lean_ctor_get(v_mctx_1865_, 7);
v_eAssignment_1881_ = lean_ctor_get(v_mctx_1865_, 8);
v_dAssignment_1882_ = lean_ctor_get(v_mctx_1865_, 9);
v_instanceTypedMVars_1883_ = lean_ctor_get(v_mctx_1865_, 10);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_mctx_1865_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1885_ = v_mctx_1865_;
v_isShared_1886_ = v_isSharedCheck_1897_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_instanceTypedMVars_1883_);
lean_inc(v_dAssignment_1882_);
lean_inc(v_eAssignment_1881_);
lean_inc(v_lAssignment_1880_);
lean_inc(v_userNames_1879_);
lean_inc(v_decls_1878_);
lean_inc(v_lDecls_1877_);
lean_inc(v_mvarCounter_1876_);
lean_inc(v_lmvarCounter_1875_);
lean_inc(v_levelAssignDepth_1874_);
lean_inc(v_depth_1873_);
lean_dec(v_mctx_1865_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1897_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1881_, v_mvarId_1860_, v_val_1861_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 8, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_depth_1873_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_levelAssignDepth_1874_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_lmvarCounter_1875_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_mvarCounter_1876_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_lDecls_1877_);
lean_ctor_set(v_reuseFailAlloc_1896_, 5, v_decls_1878_);
lean_ctor_set(v_reuseFailAlloc_1896_, 6, v_userNames_1879_);
lean_ctor_set(v_reuseFailAlloc_1896_, 7, v_lAssignment_1880_);
lean_ctor_set(v_reuseFailAlloc_1896_, 8, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 9, v_dAssignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1896_, 10, v_instanceTypedMVars_1883_);
v___x_1889_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1889_);
v___x_1891_ = v___x_1871_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_zetaDeltaFVarIds_1867_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_postponed_1868_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_diag_1869_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_put(v___y_1862_, v___x_1891_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1899_, lean_object* v_val_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1899_, v_val_1900_, v___y_1901_);
lean_dec(v___y_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; 
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc_ref(v_type_1904_);
v___x_1910_ = lean_infer_type(v_type_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l_Lean_Meta_whnfD(v_a_1911_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1947_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1947_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1947_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
switch(lean_obj_tag(v_a_1913_))
{
case 3:
{
lean_object* v_u_1917_; lean_object* v___x_1919_; 
lean_dec_ref(v_type_1904_);
v_u_1917_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_u_1917_);
lean_dec_ref_known(v_a_1913_, 1);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v_u_1917_);
v___x_1919_ = v___x_1915_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_u_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
case 2:
{
lean_object* v_mvarId_1921_; lean_object* v___x_1922_; 
lean_del_object(v___x_1915_);
v_mvarId_1921_ = lean_ctor_get(v_a_1913_, 0);
lean_inc_n(v_mvarId_1921_, 2);
lean_dec_ref_known(v_a_1913_, 1);
v___x_1922_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1921_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; uint8_t v___x_1924_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = lean_unbox(v_a_1923_);
lean_dec(v_a_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v_type_1904_);
v___x_1925_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc_n(v_a_1926_, 2);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_mkSort(v_a_1926_);
v___x_1928_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1921_, v___x_1927_, v_a_1906_);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v___x_1928_, 0);
lean_dec(v_unused_1936_);
v___x_1930_ = v___x_1928_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_dec(v___x_1928_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_a_1926_);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1926_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
lean_dec(v_mvarId_1921_);
return v___x_1925_;
}
}
else
{
lean_object* v___x_1937_; 
lean_dec(v_mvarId_1921_);
v___x_1937_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1937_;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_mvarId_1921_);
lean_dec_ref(v_type_1904_);
v_a_1938_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1922_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1922_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
default: 
{
lean_object* v___x_1946_; 
lean_del_object(v___x_1915_);
lean_dec(v_a_1913_);
v___x_1946_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_type_1904_);
v_a_1948_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1912_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1912_);
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
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_type_1904_);
v_a_1956_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1910_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1910_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Meta_getLevel(v_type_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1971_, lean_object* v_val_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1971_, v_val_1972_, v___y_1974_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1979_, lean_object* v_val_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1979_, v_val_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1988_, v_x_1989_, v_x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1992_, lean_object* v_x_1993_, size_t v_x_1994_, size_t v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1993_, v_x_1994_, v_x_1995_, v_x_1996_, v_x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
size_t v_x_1495__boxed_2005_; size_t v_x_1496__boxed_2006_; lean_object* v_res_2007_; 
v_x_1495__boxed_2005_ = lean_unbox_usize(v_x_2001_);
lean_dec(v_x_2001_);
v_x_1496__boxed_2006_ = lean_unbox_usize(v_x_2002_);
lean_dec(v_x_2002_);
v_res_2007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1999_, v_x_2000_, v_x_1495__boxed_2005_, v_x_1496__boxed_2006_, v_x_2003_, v_x_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2008_, lean_object* v_n_2009_, lean_object* v_k_2010_, lean_object* v_v_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2009_, v_k_2010_, v_v_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2013_, size_t v_depth_2014_, lean_object* v_keys_2015_, lean_object* v_vals_2016_, lean_object* v_heq_2017_, lean_object* v_i_2018_, lean_object* v_entries_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2014_, v_keys_2015_, v_vals_2016_, v_i_2018_, v_entries_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2021_, lean_object* v_depth_2022_, lean_object* v_keys_2023_, lean_object* v_vals_2024_, lean_object* v_heq_2025_, lean_object* v_i_2026_, lean_object* v_entries_2027_){
_start:
{
size_t v_depth_boxed_2028_; lean_object* v_res_2029_; 
v_depth_boxed_2028_ = lean_unbox_usize(v_depth_2022_);
lean_dec(v_depth_2022_);
v_res_2029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2021_, v_depth_boxed_2028_, v_keys_2023_, v_vals_2024_, v_heq_2025_, v_i_2026_, v_entries_2027_);
lean_dec_ref(v_vals_2024_);
lean_dec_ref(v_keys_2023_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2031_, v_x_2032_, v_x_2033_, v_x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2036_, lean_object* v_b_2037_, lean_object* v_c_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
v___x_2044_ = lean_apply_7(v_k_2036_, v_b_2037_, v_c_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, lean_box(0));
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2045_, lean_object* v_b_2046_, lean_object* v_c_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2045_, v_b_2046_, v_c_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2054_, lean_object* v_k_2055_, uint8_t v_cleanupAnnotations_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___f_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___f_2062_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2062_, 0, v_k_2055_);
v___x_2063_ = 0;
v___x_2064_ = lean_box(0);
v___x_2065_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2063_, v___x_2064_, v_type_2054_, v___f_2062_, v_cleanupAnnotations_2056_, v___x_2063_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2065_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2065_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2082_, lean_object* v_k_2083_, lean_object* v_cleanupAnnotations_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2090_; lean_object* v_res_2091_; 
v_cleanupAnnotations_boxed_2090_ = lean_unbox(v_cleanupAnnotations_2084_);
v_res_2091_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2082_, v_k_2083_, v_cleanupAnnotations_boxed_2090_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2092_, lean_object* v_type_2093_, lean_object* v_k_2094_, uint8_t v_cleanupAnnotations_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2093_, v_k_2094_, v_cleanupAnnotations_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_type_2103_, lean_object* v_k_2104_, lean_object* v_cleanupAnnotations_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2111_; lean_object* v_res_2112_; 
v_cleanupAnnotations_boxed_2111_ = lean_unbox(v_cleanupAnnotations_2105_);
v_res_2112_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2102_, v_type_2103_, v_k_2104_, v_cleanupAnnotations_boxed_2111_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2113_, size_t v_i_2114_, size_t v_stop_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_usize_dec_eq(v_i_2114_, v_stop_2115_);
if (v___x_2122_ == 0)
{
size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = ((size_t)1ULL);
v___x_2124_ = lean_usize_sub(v_i_2114_, v___x_2123_);
v___x_2125_ = lean_array_uget_borrowed(v_as_2113_, v___x_2124_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___x_2125_);
v___x_2126_ = lean_infer_type(v___x_2125_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Meta_getLevel(v_a_2127_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_mkLevelIMax_x27(v_a_2129_, v_b_2116_);
v_i_2114_ = v___x_2124_;
v_b_2116_ = v___x_2130_;
goto _start;
}
else
{
lean_dec(v_b_2116_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2128_, 1);
v_i_2114_ = v___x_2124_;
v_b_2116_ = v_a_2132_;
goto _start;
}
else
{
return v___x_2128_;
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_b_2116_);
v_a_2134_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2126_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2126_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_b_2116_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2143_, lean_object* v_i_2144_, lean_object* v_stop_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
size_t v_i_boxed_2152_; size_t v_stop_boxed_2153_; lean_object* v_res_2154_; 
v_i_boxed_2152_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_stop_boxed_2153_ = lean_unbox_usize(v_stop_2145_);
lean_dec(v_stop_2145_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2143_, v_i_boxed_2152_, v_stop_boxed_2153_, v_b_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_as_2143_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2155_, lean_object* v_e_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___y_2163_; lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Meta_getLevel(v_e_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
v___x_2184_ = lean_array_get_size(v_xs_2155_);
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v___x_2184_);
if (v___x_2186_ == 0)
{
lean_dec(v_a_2183_);
v___y_2163_ = v___x_2182_;
goto v___jp_2162_;
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
lean_dec_ref_known(v___x_2182_, 1);
v___x_2187_ = lean_usize_of_nat(v___x_2184_);
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2155_, v___x_2187_, v___x_2188_, v_a_2183_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
v___y_2163_ = v___x_2189_;
goto v___jp_2162_;
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_a_2190_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2182_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2182_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
v___jp_2162_:
{
if (lean_obj_tag(v___y_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2173_; 
v_a_2164_ = lean_ctor_get(v___y_2163_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___y_2163_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2166_ = v___y_2163_;
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___y_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2168_ = l_Lean_Level_normalize(v_a_2164_);
lean_dec(v_a_2164_);
v___x_2169_ = l_Lean_mkSort(v___x_2168_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_a_2174_ = lean_ctor_get(v___y_2163_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___y_2163_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___y_2163_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___y_2163_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2198_, lean_object* v_e_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2198_, v_e_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_xs_2198_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___f_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; 
v___f_2213_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2214_ = 0;
v___x_2215_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2207_, v___f_2213_, v___x_2214_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2223_, lean_object* v_k_2224_, uint8_t v_cleanupAnnotations_2225_, uint8_t v_preserveNondepLet_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___f_2232_; uint8_t v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2232_, 0, v_k_2224_);
v___x_2233_ = 1;
v___x_2234_ = 0;
v___x_2235_ = lean_box(0);
v___x_2236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2223_, v___x_2233_, v___x_2233_, v_preserveNondepLet_2226_, v___x_2234_, v___x_2235_, v___f_2232_, v_cleanupAnnotations_2225_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
v_a_2245_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2236_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2236_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2253_, lean_object* v_k_2254_, lean_object* v_cleanupAnnotations_2255_, lean_object* v_preserveNondepLet_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2262_; uint8_t v_preserveNondepLet_boxed_2263_; lean_object* v_res_2264_; 
v_cleanupAnnotations_boxed_2262_ = lean_unbox(v_cleanupAnnotations_2255_);
v_preserveNondepLet_boxed_2263_ = lean_unbox(v_preserveNondepLet_2256_);
v_res_2264_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2253_, v_k_2254_, v_cleanupAnnotations_boxed_2262_, v_preserveNondepLet_boxed_2263_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2265_, lean_object* v_e_2266_, lean_object* v_k_2267_, uint8_t v_cleanupAnnotations_2268_, uint8_t v_preserveNondepLet_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2266_, v_k_2267_, v_cleanupAnnotations_2268_, v_preserveNondepLet_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_e_2277_, lean_object* v_k_2278_, lean_object* v_cleanupAnnotations_2279_, lean_object* v_preserveNondepLet_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2286_; uint8_t v_preserveNondepLet_boxed_2287_; lean_object* v_res_2288_; 
v_cleanupAnnotations_boxed_2286_ = lean_unbox(v_cleanupAnnotations_2279_);
v_preserveNondepLet_boxed_2287_ = lean_unbox(v_preserveNondepLet_2280_);
v_res_2288_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2276_, v_e_2277_, v_k_2278_, v_cleanupAnnotations_boxed_2286_, v_preserveNondepLet_boxed_2287_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2289_, lean_object* v_e_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
v___x_2296_ = lean_infer_type(v_e_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; uint8_t v___x_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = 0;
v___x_2299_ = 1;
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Meta_mkForallFVars(v_xs_2289_, v_a_2297_, v___x_2298_, v___x_2299_, v___x_2298_, v___x_2300_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2301_;
}
else
{
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2302_, lean_object* v_e_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2302_, v_e_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_xs_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___f_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v___f_2317_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2318_ = 0;
v___x_2319_ = 1;
v___x_2320_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2311_, v___f_2317_, v___x_2318_, v___x_2319_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2327_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2340_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2341_ = l_Lean_MessageData_ofName(v_mvarId_2334_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2344_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2353_, lean_object* v_mvarId_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2361_, lean_object* v_mvarId_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2361_, v_mvarId_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v_mctx_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_st_ref_get(v_a_2371_);
v_mctx_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc_ref(v_mctx_2376_);
lean_dec(v___x_2375_);
v___x_2377_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2376_, v_mvarId_2369_);
lean_dec_ref(v_mctx_2376_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_mvarId_2369_);
v_val_2379_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v___x_2377_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v___x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_type_2383_; lean_object* v___x_2385_; 
v_type_2383_ = lean_ctor_get(v_val_2379_, 2);
lean_inc_ref(v_type_2383_);
lean_dec(v_val_2379_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 0);
lean_ctor_set(v___x_2381_, 0, v_type_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_type_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_lctx_2400_; lean_object* v___x_2401_; 
v_lctx_2400_ = lean_ctor_get(v_a_2396_, 2);
lean_inc(v_fvarId_2395_);
lean_inc_ref(v_lctx_2400_);
v___x_2401_ = lean_local_ctx_find(v_lctx_2400_, v_fvarId_2395_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2395_, v_a_2397_, v_a_2398_);
return v___x_2402_;
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_fvarId_2395_);
v_val_2403_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_val_2403_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2411_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = l_Lean_LocalDecl_type(v_val_2403_);
lean_dec(v_val_2403_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2407_);
v___x_2409_ = v___x_2405_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2418_, v_a_2419_, v_a_2421_, v_a_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2431_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_instMonadEIO(lean_box(0));
return v___x_2432_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2434_ = l_StateRefT_x27_instMonad___redArg(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___f_2439_; 
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2439_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2439_, 0, v___x_2438_);
return v___f_2439_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___f_2441_; 
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2441_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2441_, 0, v___x_2440_);
return v___f_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; 
v___f_2442_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2443_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___f_2443_);
lean_ctor_set(v___x_2444_, 1, v___f_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___f_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2446_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2446_, 0, v___x_2445_);
return v___f_2446_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___f_2448_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2448_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2448_, 0, v___x_2447_);
return v___f_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v___f_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2450_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___f_2450_);
lean_ctor_set(v___x_2451_, 1, v___f_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2454_, lean_object* v_inferType_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
uint8_t v_cacheInferType_2500_; 
v_cacheInferType_2500_ = lean_ctor_get_uint8(v_a_2456_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2500_ == 0)
{
lean_dec_ref(v_e_2454_);
goto v___jp_2461_;
}
else
{
uint8_t v___x_2501_; 
v___x_2501_ = l_Lean_Expr_hasMVar(v_e_2454_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2454_, v_a_2456_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2602_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2602_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2602_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v_cache_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2597_; 
v___x_2507_ = lean_st_ref_get(v_a_2457_);
v_cache_2508_ = lean_ctor_get(v___x_2507_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2598_ = lean_ctor_get(v___x_2507_, 4);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v___x_2507_, 3);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v___x_2507_, 2);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v___x_2507_, 0);
lean_dec(v_unused_2601_);
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2597_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_cache_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2597_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_inferType_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___x_2555_; 
v_inferType_2512_ = lean_ctor_get(v_cache_2508_, 0);
lean_inc_ref(v_inferType_2512_);
lean_dec_ref(v_cache_2508_);
v___f_2513_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2514_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2503_);
v___x_2555_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2513_, v___x_2514_, v_inferType_2512_, v_a_2503_);
lean_dec_ref(v_inferType_2512_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2556_; lean_object* v_toApplicative_2557_; lean_object* v_toFunctor_2558_; lean_object* v_toSeq_2559_; lean_object* v_toSeqLeft_2560_; lean_object* v_toSeqRight_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___x_2571_; 
lean_del_object(v___x_2505_);
v___x_2556_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2557_ = lean_ctor_get(v___x_2556_, 0);
v_toFunctor_2558_ = lean_ctor_get(v_toApplicative_2557_, 0);
v_toSeq_2559_ = lean_ctor_get(v_toApplicative_2557_, 2);
v_toSeqLeft_2560_ = lean_ctor_get(v_toApplicative_2557_, 3);
v_toSeqRight_2561_ = lean_ctor_get(v_toApplicative_2557_, 4);
v___f_2562_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2563_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2558_, 2);
v___f_2564_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2564_, 0, v_toFunctor_2558_);
v___f_2565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2565_, 0, v_toFunctor_2558_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___f_2564_);
lean_ctor_set(v___x_2566_, 1, v___f_2565_);
lean_inc(v_toSeqRight_2561_);
v___f_2567_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2567_, 0, v_toSeqRight_2561_);
lean_inc(v_toSeqLeft_2560_);
v___f_2568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2568_, 0, v_toSeqLeft_2560_);
lean_inc(v_toSeq_2559_);
v___f_2569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2569_, 0, v_toSeq_2559_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 4, v___f_2567_);
lean_ctor_set(v___x_2510_, 3, v___f_2568_);
lean_ctor_set(v___x_2510_, 2, v___f_2569_);
lean_ctor_set(v___x_2510_, 1, v___f_2562_);
lean_ctor_set(v___x_2510_, 0, v___x_2566_);
v___x_2571_ = v___x_2510_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___f_2562_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v___f_2569_);
lean_ctor_set(v_reuseFailAlloc_2592_, 3, v___f_2568_);
lean_ctor_set(v_reuseFailAlloc_2592_, 4, v___f_2567_);
v___x_2571_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_toCold_2578_; lean_object* v_cancelTk_x3f_2579_; 
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___f_2563_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2574_ = l_Lean_Core_instMonadRefCoreM;
v___x_2575_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2576_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2575_, v___x_2572_);
v___x_2577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2574_);
lean_ctor_set(v___x_2577_, 2, v___x_2576_);
v_toCold_2578_ = lean_ctor_get(v_a_2458_, 0);
v_cancelTk_x3f_2579_ = lean_ctor_get(v_toCold_2578_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2579_) == 1)
{
lean_object* v_val_2580_; uint8_t v___x_2581_; 
v_val_2580_ = lean_ctor_get(v_cancelTk_x3f_2579_, 0);
v___x_2581_ = l_IO_CancelToken_isSet(v_val_2580_);
if (v___x_2581_ == 0)
{
lean_dec_ref_known(v___x_2577_, 3);
goto v___jp_2515_;
}
else
{
lean_object* v___x_1999__overap_2582_; lean_object* v___x_2583_; 
v___x_1999__overap_2582_ = l_Lean_throwInterruptException___redArg(v___x_2577_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2583_ = lean_apply_3(v___x_1999__overap_2582_, v_a_2458_, v_a_2459_, lean_box(0));
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_dec_ref_known(v___x_2583_, 1);
goto v___jp_2515_;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_a_2503_);
lean_dec_ref(v_inferType_2455_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2577_, 3);
goto v___jp_2515_;
}
}
}
else
{
lean_object* v_val_2593_; lean_object* v___x_2595_; 
lean_del_object(v___x_2510_);
lean_dec(v_a_2503_);
lean_dec_ref(v_inferType_2455_);
v_val_2593_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v___x_2555_, 1);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v_val_2593_);
v___x_2595_ = v___x_2505_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
v___jp_2515_:
{
lean_object* v___x_2516_; 
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
v___x_2516_ = lean_apply_5(v_inferType_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, lean_box(0));
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; uint8_t v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
v___x_2518_ = l_Lean_Expr_hasMVar(v_a_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2554_);
v___x_2520_ = v___x_2516_;
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v_cache_2523_; lean_object* v_mctx_2524_; lean_object* v_zetaDeltaFVarIds_2525_; lean_object* v_postponed_2526_; lean_object* v_diag_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2552_; 
v___x_2522_ = lean_st_ref_take(v_a_2457_);
v_cache_2523_ = lean_ctor_get(v___x_2522_, 1);
v_mctx_2524_ = lean_ctor_get(v___x_2522_, 0);
v_zetaDeltaFVarIds_2525_ = lean_ctor_get(v___x_2522_, 2);
v_postponed_2526_ = lean_ctor_get(v___x_2522_, 3);
v_diag_2527_ = lean_ctor_get(v___x_2522_, 4);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2529_ = v___x_2522_;
v_isShared_2530_ = v_isSharedCheck_2552_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_diag_2527_);
lean_inc(v_postponed_2526_);
lean_inc(v_zetaDeltaFVarIds_2525_);
lean_inc(v_cache_2523_);
lean_inc(v_mctx_2524_);
lean_dec(v___x_2522_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2552_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_inferType_2531_; lean_object* v_funInfo_2532_; lean_object* v_synthInstance_2533_; lean_object* v_whnf_2534_; lean_object* v_defEqTrans_2535_; lean_object* v_defEqPerm_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2551_; 
v_inferType_2531_ = lean_ctor_get(v_cache_2523_, 0);
v_funInfo_2532_ = lean_ctor_get(v_cache_2523_, 1);
v_synthInstance_2533_ = lean_ctor_get(v_cache_2523_, 2);
v_whnf_2534_ = lean_ctor_get(v_cache_2523_, 3);
v_defEqTrans_2535_ = lean_ctor_get(v_cache_2523_, 4);
v_defEqPerm_2536_ = lean_ctor_get(v_cache_2523_, 5);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_cache_2523_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2538_ = v_cache_2523_;
v_isShared_2539_ = v_isSharedCheck_2551_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_defEqPerm_2536_);
lean_inc(v_defEqTrans_2535_);
lean_inc(v_whnf_2534_);
lean_inc(v_synthInstance_2533_);
lean_inc(v_funInfo_2532_);
lean_inc(v_inferType_2531_);
lean_dec(v_cache_2523_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2551_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_inc(v_a_2517_);
v___x_2540_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2513_, v___x_2514_, v_inferType_2531_, v_a_2503_, v_a_2517_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_funInfo_2532_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_synthInstance_2533_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_whnf_2534_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_defEqTrans_2535_);
lean_ctor_set(v_reuseFailAlloc_2550_, 5, v_defEqPerm_2536_);
v___x_2542_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2542_);
v___x_2544_ = v___x_2529_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_mctx_2524_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_zetaDeltaFVarIds_2525_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_postponed_2526_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_diag_2527_);
v___x_2544_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_st_ref_put(v_a_2457_, v___x_2544_);
if (v_isShared_2521_ == 0)
{
v___x_2547_ = v___x_2520_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2517_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2517_);
lean_dec(v_a_2503_);
return v___x_2516_;
}
}
else
{
lean_dec(v_a_2503_);
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_inferType_2455_);
v_a_2603_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2502_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2502_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_dec_ref(v_e_2454_);
goto v___jp_2461_;
}
}
v___jp_2461_:
{
lean_object* v___x_2462_; lean_object* v_toApplicative_2463_; lean_object* v_toFunctor_2464_; lean_object* v_toSeq_2465_; lean_object* v_toSeqLeft_2466_; lean_object* v_toSeqRight_2467_; lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_toCold_2483_; lean_object* v_cancelTk_x3f_2484_; 
v___x_2462_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2463_ = lean_ctor_get(v___x_2462_, 0);
v_toFunctor_2464_ = lean_ctor_get(v_toApplicative_2463_, 0);
v_toSeq_2465_ = lean_ctor_get(v_toApplicative_2463_, 2);
v_toSeqLeft_2466_ = lean_ctor_get(v_toApplicative_2463_, 3);
v_toSeqRight_2467_ = lean_ctor_get(v_toApplicative_2463_, 4);
v___f_2468_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2469_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2464_, 2);
v___f_2470_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2470_, 0, v_toFunctor_2464_);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toFunctor_2464_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___f_2470_);
lean_ctor_set(v___x_2472_, 1, v___f_2471_);
lean_inc(v_toSeqRight_2467_);
v___f_2473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2473_, 0, v_toSeqRight_2467_);
lean_inc(v_toSeqLeft_2466_);
v___f_2474_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2474_, 0, v_toSeqLeft_2466_);
lean_inc(v_toSeq_2465_);
v___f_2475_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2475_, 0, v_toSeq_2465_);
v___x_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2472_);
lean_ctor_set(v___x_2476_, 1, v___f_2468_);
lean_ctor_set(v___x_2476_, 2, v___f_2475_);
lean_ctor_set(v___x_2476_, 3, v___f_2474_);
lean_ctor_set(v___x_2476_, 4, v___f_2473_);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v___f_2469_);
v___x_2478_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2479_ = l_Lean_Core_instMonadRefCoreM;
v___x_2480_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2481_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2480_, v___x_2477_);
v___x_2482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2478_);
lean_ctor_set(v___x_2482_, 1, v___x_2479_);
lean_ctor_set(v___x_2482_, 2, v___x_2481_);
v_toCold_2483_ = lean_ctor_get(v_a_2458_, 0);
v_cancelTk_x3f_2484_ = lean_ctor_get(v_toCold_2483_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2484_) == 1)
{
lean_object* v_val_2485_; uint8_t v___x_2486_; 
v_val_2485_ = lean_ctor_get(v_cancelTk_x3f_2484_, 0);
v___x_2486_ = l_IO_CancelToken_isSet(v_val_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec_ref_known(v___x_2482_, 3);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
v___x_2487_ = lean_apply_5(v_inferType_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, lean_box(0));
return v___x_2487_;
}
else
{
lean_object* v___x_1711__overap_2488_; lean_object* v___x_2489_; 
v___x_1711__overap_2488_ = l_Lean_throwInterruptException___redArg(v___x_2482_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2489_ = lean_apply_3(v___x_1711__overap_2488_, v_a_2458_, v_a_2459_, lean_box(0));
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; 
lean_dec_ref_known(v___x_2489_, 1);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
v___x_2490_ = lean_apply_5(v_inferType_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, lean_box(0));
return v___x_2490_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_inferType_2455_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2489_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2482_, 3);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
lean_inc(v_a_2457_);
lean_inc_ref(v_a_2456_);
v___x_2499_ = lean_apply_5(v_inferType_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, lean_box(0));
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2611_, lean_object* v_inferType_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2611_, v_inferType_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2618_;
}
}
static lean_object* _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = 2;
v___x_2620_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2673_; uint8_t v_beta_2674_; 
v___x_2673_ = l_Lean_Meta_Context_config(v___y_2622_);
v_beta_2674_ = lean_ctor_get_uint8(v___x_2673_, 13);
if (v_beta_2674_ == 0)
{
lean_dec_ref(v___x_2673_);
goto v___jp_2627_;
}
else
{
uint8_t v_iota_2675_; 
v_iota_2675_ = lean_ctor_get_uint8(v___x_2673_, 12);
if (v_iota_2675_ == 0)
{
lean_dec_ref(v___x_2673_);
goto v___jp_2627_;
}
else
{
uint8_t v_zeta_2676_; 
v_zeta_2676_ = lean_ctor_get_uint8(v___x_2673_, 15);
if (v_zeta_2676_ == 0)
{
lean_dec_ref(v___x_2673_);
goto v___jp_2627_;
}
else
{
uint8_t v_zetaHave_2677_; 
v_zetaHave_2677_ = lean_ctor_get_uint8(v___x_2673_, 18);
if (v_zetaHave_2677_ == 0)
{
lean_dec_ref(v___x_2673_);
goto v___jp_2627_;
}
else
{
uint8_t v_zetaDelta_2678_; 
v_zetaDelta_2678_ = lean_ctor_get_uint8(v___x_2673_, 16);
if (v_zetaDelta_2678_ == 0)
{
lean_dec_ref(v___x_2673_);
goto v___jp_2627_;
}
else
{
uint8_t v_etaStruct_2679_; uint8_t v_proj_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_etaStruct_2679_ = lean_ctor_get_uint8(v___x_2673_, 10);
v_proj_2680_ = lean_ctor_get_uint8(v___x_2673_, 14);
lean_dec_ref(v___x_2673_);
v___x_2681_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2680_);
v___x_2682_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_2683_ = lean_nat_dec_eq(v___x_2681_, v___x_2682_);
lean_dec(v___x_2681_);
if (v___x_2683_ == 0)
{
goto v___jp_2627_;
}
else
{
uint8_t v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = 0;
v___x_2685_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2679_, v___x_2684_);
if (v___x_2685_ == 0)
{
goto v___jp_2627_;
}
else
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_apply_5(v_x_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, lean_box(0));
return v___x_2686_;
}
}
}
}
}
}
}
v___jp_2627_:
{
lean_object* v___x_2628_; uint8_t v_foApprox_2629_; uint8_t v_ctxApprox_2630_; uint8_t v_quasiPatternApprox_2631_; uint8_t v_constApprox_2632_; uint8_t v_isDefEqStuckEx_2633_; uint8_t v_unificationHints_2634_; uint8_t v_proofIrrelevance_2635_; uint8_t v_assignSyntheticOpaque_2636_; uint8_t v_offsetCnstrs_2637_; uint8_t v_transparency_2638_; uint8_t v_univApprox_2639_; uint8_t v_zetaUnused_2640_; uint8_t v_canUnfoldPredicateConfig_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2672_; 
v___x_2628_ = l_Lean_Meta_Context_config(v___y_2622_);
v_foApprox_2629_ = lean_ctor_get_uint8(v___x_2628_, 0);
v_ctxApprox_2630_ = lean_ctor_get_uint8(v___x_2628_, 1);
v_quasiPatternApprox_2631_ = lean_ctor_get_uint8(v___x_2628_, 2);
v_constApprox_2632_ = lean_ctor_get_uint8(v___x_2628_, 3);
v_isDefEqStuckEx_2633_ = lean_ctor_get_uint8(v___x_2628_, 4);
v_unificationHints_2634_ = lean_ctor_get_uint8(v___x_2628_, 5);
v_proofIrrelevance_2635_ = lean_ctor_get_uint8(v___x_2628_, 6);
v_assignSyntheticOpaque_2636_ = lean_ctor_get_uint8(v___x_2628_, 7);
v_offsetCnstrs_2637_ = lean_ctor_get_uint8(v___x_2628_, 8);
v_transparency_2638_ = lean_ctor_get_uint8(v___x_2628_, 9);
v_univApprox_2639_ = lean_ctor_get_uint8(v___x_2628_, 11);
v_zetaUnused_2640_ = lean_ctor_get_uint8(v___x_2628_, 17);
v_canUnfoldPredicateConfig_2641_ = lean_ctor_get_uint8(v___x_2628_, 19);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2643_ = v___x_2628_;
v_isShared_2644_ = v_isSharedCheck_2672_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2628_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2672_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
uint8_t v___x_2645_; uint8_t v___x_2646_; uint8_t v___x_2647_; lean_object* v___x_2649_; 
v___x_2645_ = 1;
v___x_2646_ = 0;
v___x_2647_ = 2;
if (v_isShared_2644_ == 0)
{
v___x_2649_ = v___x_2643_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 0, v_foApprox_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 1, v_ctxApprox_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 2, v_quasiPatternApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 3, v_constApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 4, v_isDefEqStuckEx_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 5, v_unificationHints_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 6, v_proofIrrelevance_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 7, v_assignSyntheticOpaque_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 8, v_offsetCnstrs_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 9, v_transparency_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 11, v_univApprox_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 17, v_zetaUnused_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2671_, 19, v_canUnfoldPredicateConfig_2641_);
v___x_2649_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
uint8_t v_trackZetaDelta_2650_; lean_object* v_zetaDeltaSet_2651_; lean_object* v_lctx_2652_; lean_object* v_localInstances_2653_; lean_object* v_defEqCtx_x3f_2654_; lean_object* v_synthPendingDepth_2655_; lean_object* v_customCanUnfoldPredicate_x3f_2656_; uint8_t v_univApprox_2657_; uint8_t v_inTypeClassResolution_2658_; uint8_t v_cacheInferType_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2669_; 
lean_ctor_set_uint8(v___x_2649_, 10, v___x_2646_);
lean_ctor_set_uint8(v___x_2649_, 12, v___x_2645_);
lean_ctor_set_uint8(v___x_2649_, 13, v___x_2645_);
lean_ctor_set_uint8(v___x_2649_, 14, v___x_2647_);
lean_ctor_set_uint8(v___x_2649_, 15, v___x_2645_);
lean_ctor_set_uint8(v___x_2649_, 16, v___x_2645_);
lean_ctor_set_uint8(v___x_2649_, 18, v___x_2645_);
v_trackZetaDelta_2650_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7);
v_zetaDeltaSet_2651_ = lean_ctor_get(v___y_2622_, 1);
v_lctx_2652_ = lean_ctor_get(v___y_2622_, 2);
v_localInstances_2653_ = lean_ctor_get(v___y_2622_, 3);
v_defEqCtx_x3f_2654_ = lean_ctor_get(v___y_2622_, 4);
v_synthPendingDepth_2655_ = lean_ctor_get(v___y_2622_, 5);
v_customCanUnfoldPredicate_x3f_2656_ = lean_ctor_get(v___y_2622_, 6);
v_univApprox_2657_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2658_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 2);
v_cacheInferType_2659_ = lean_ctor_get_uint8(v___y_2622_, sizeof(void*)*7 + 3);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___y_2622_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v___y_2622_, 0);
lean_dec(v_unused_2670_);
v___x_2661_ = v___y_2622_;
v_isShared_2662_ = v_isSharedCheck_2669_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2656_);
lean_inc(v_synthPendingDepth_2655_);
lean_inc(v_defEqCtx_x3f_2654_);
lean_inc(v_localInstances_2653_);
lean_inc(v_lctx_2652_);
lean_inc(v_zetaDeltaSet_2651_);
lean_dec(v___y_2622_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2669_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint64_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2649_);
v___x_2664_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2664_, 0, v___x_2649_);
lean_ctor_set_uint64(v___x_2664_, sizeof(void*)*1, v___x_2663_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_zetaDeltaSet_2651_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_lctx_2652_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_localInstances_2653_);
lean_ctor_set(v_reuseFailAlloc_2668_, 4, v_defEqCtx_x3f_2654_);
lean_ctor_set(v_reuseFailAlloc_2668_, 5, v_synthPendingDepth_2655_);
lean_ctor_set(v_reuseFailAlloc_2668_, 6, v_customCanUnfoldPredicate_x3f_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*7, v_trackZetaDelta_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*7 + 1, v_univApprox_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*7 + 3, v_cacheInferType_2659_);
v___x_2666_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_apply_5(v_x_2621_, v___x_2666_, v___y_2623_, v___y_2624_, v___y_2625_, lean_box(0));
return v___x_2667_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___y_2701_; lean_object* v___x_2718_; uint8_t v_transparency_2719_; uint8_t v___x_2720_; uint8_t v___x_2721_; 
v___x_2718_ = l_Lean_Meta_Context_config(v_a_2695_);
v_transparency_2719_ = lean_ctor_get_uint8(v___x_2718_, 9);
lean_dec_ref(v___x_2718_);
v___x_2720_ = 1;
v___x_2721_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; 
lean_inc(v_a_2698_);
lean_inc_ref(v_a_2697_);
lean_inc(v_a_2696_);
lean_inc_ref(v_a_2695_);
v___x_2722_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
v___y_2701_ = v___x_2722_;
goto v___jp_2700_;
}
else
{
lean_object* v_keyedConfig_2723_; uint8_t v_trackZetaDelta_2724_; lean_object* v_zetaDeltaSet_2725_; lean_object* v_lctx_2726_; lean_object* v_localInstances_2727_; lean_object* v_defEqCtx_x3f_2728_; lean_object* v_synthPendingDepth_2729_; lean_object* v_customCanUnfoldPredicate_x3f_2730_; uint8_t v_univApprox_2731_; uint8_t v_inTypeClassResolution_2732_; uint8_t v_cacheInferType_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_keyedConfig_2723_ = lean_ctor_get(v_a_2695_, 0);
v_trackZetaDelta_2724_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*7);
v_zetaDeltaSet_2725_ = lean_ctor_get(v_a_2695_, 1);
v_lctx_2726_ = lean_ctor_get(v_a_2695_, 2);
v_localInstances_2727_ = lean_ctor_get(v_a_2695_, 3);
v_defEqCtx_x3f_2728_ = lean_ctor_get(v_a_2695_, 4);
v_synthPendingDepth_2729_ = lean_ctor_get(v_a_2695_, 5);
v_customCanUnfoldPredicate_x3f_2730_ = lean_ctor_get(v_a_2695_, 6);
v_univApprox_2731_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2732_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*7 + 2);
v_cacheInferType_2733_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2723_);
v___x_2734_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2720_, v_keyedConfig_2723_);
lean_inc(v_customCanUnfoldPredicate_x3f_2730_);
lean_inc(v_synthPendingDepth_2729_);
lean_inc(v_defEqCtx_x3f_2728_);
lean_inc_ref(v_localInstances_2727_);
lean_inc_ref(v_lctx_2726_);
lean_inc(v_zetaDeltaSet_2725_);
v___x_2735_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v_zetaDeltaSet_2725_);
lean_ctor_set(v___x_2735_, 2, v_lctx_2726_);
lean_ctor_set(v___x_2735_, 3, v_localInstances_2727_);
lean_ctor_set(v___x_2735_, 4, v_defEqCtx_x3f_2728_);
lean_ctor_set(v___x_2735_, 5, v_synthPendingDepth_2729_);
lean_ctor_set(v___x_2735_, 6, v_customCanUnfoldPredicate_x3f_2730_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7, v_trackZetaDelta_2724_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 1, v_univApprox_2731_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2732_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*7 + 3, v_cacheInferType_2733_);
lean_inc(v_a_2698_);
lean_inc_ref(v_a_2697_);
lean_inc(v_a_2696_);
v___x_2736_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2694_, v___x_2735_, v_a_2696_, v_a_2697_, v_a_2698_);
v___y_2701_ = v___x_2736_;
goto v___jp_2700_;
}
v___jp_2700_:
{
if (lean_obj_tag(v___y_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___y_2701_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___y_2701_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___y_2701_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___y_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_a_2710_ = lean_ctor_get(v___y_2701_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___y_2701_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___y_2701_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___y_2701_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2744_, lean_object* v_x_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___y_2752_; lean_object* v___x_2769_; uint8_t v_transparency_2770_; uint8_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2769_ = l_Lean_Meta_Context_config(v_a_2746_);
v_transparency_2770_ = lean_ctor_get_uint8(v___x_2769_, 9);
lean_dec_ref(v___x_2769_);
v___x_2771_ = 1;
v___x_2772_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2770_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
lean_inc_ref(v_a_2746_);
v___x_2773_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
v___y_2752_ = v___x_2773_;
goto v___jp_2751_;
}
else
{
lean_object* v_keyedConfig_2774_; uint8_t v_trackZetaDelta_2775_; lean_object* v_zetaDeltaSet_2776_; lean_object* v_lctx_2777_; lean_object* v_localInstances_2778_; lean_object* v_defEqCtx_x3f_2779_; lean_object* v_synthPendingDepth_2780_; lean_object* v_customCanUnfoldPredicate_x3f_2781_; uint8_t v_univApprox_2782_; uint8_t v_inTypeClassResolution_2783_; uint8_t v_cacheInferType_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_keyedConfig_2774_ = lean_ctor_get(v_a_2746_, 0);
v_trackZetaDelta_2775_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7);
v_zetaDeltaSet_2776_ = lean_ctor_get(v_a_2746_, 1);
v_lctx_2777_ = lean_ctor_get(v_a_2746_, 2);
v_localInstances_2778_ = lean_ctor_get(v_a_2746_, 3);
v_defEqCtx_x3f_2779_ = lean_ctor_get(v_a_2746_, 4);
v_synthPendingDepth_2780_ = lean_ctor_get(v_a_2746_, 5);
v_customCanUnfoldPredicate_x3f_2781_ = lean_ctor_get(v_a_2746_, 6);
v_univApprox_2782_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2783_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 2);
v_cacheInferType_2784_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2774_);
v___x_2785_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2771_, v_keyedConfig_2774_);
lean_inc(v_customCanUnfoldPredicate_x3f_2781_);
lean_inc(v_synthPendingDepth_2780_);
lean_inc(v_defEqCtx_x3f_2779_);
lean_inc_ref(v_localInstances_2778_);
lean_inc_ref(v_lctx_2777_);
lean_inc(v_zetaDeltaSet_2776_);
v___x_2786_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_zetaDeltaSet_2776_);
lean_ctor_set(v___x_2786_, 2, v_lctx_2777_);
lean_ctor_set(v___x_2786_, 3, v_localInstances_2778_);
lean_ctor_set(v___x_2786_, 4, v_defEqCtx_x3f_2779_);
lean_ctor_set(v___x_2786_, 5, v_synthPendingDepth_2780_);
lean_ctor_set(v___x_2786_, 6, v_customCanUnfoldPredicate_x3f_2781_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7, v_trackZetaDelta_2775_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 1, v_univApprox_2782_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2783_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 3, v_cacheInferType_2784_);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
v___x_2787_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2745_, v___x_2786_, v_a_2747_, v_a_2748_, v_a_2749_);
v___y_2752_ = v___x_2787_;
goto v___jp_2751_;
}
v___jp_2751_:
{
if (lean_obj_tag(v___y_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_a_2753_ = lean_ctor_get(v___y_2752_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___y_2752_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___y_2752_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___y_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___y_2752_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___y_2752_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___y_2752_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___y_2752_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2788_, lean_object* v_x_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2788_, v_x_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2795_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = l_Lean_interruptExceptionId;
v___x_2798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___x_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_){
_start:
{
lean_object* v_ks_2818_; lean_object* v_vs_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2848_; 
v_ks_2818_ = lean_ctor_get(v_x_2814_, 0);
v_vs_2819_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2821_ = v_x_2814_;
v_isShared_2822_ = v_isSharedCheck_2848_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_vs_2819_);
lean_inc(v_ks_2818_);
lean_dec(v_x_2814_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2848_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
uint8_t v___y_2824_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = lean_array_get_size(v_ks_2818_);
v___x_2837_ = lean_nat_dec_lt(v_x_2815_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_del_object(v___x_2821_);
lean_dec(v_x_2815_);
v___x_2838_ = lean_array_push(v_ks_2818_, v_x_2816_);
v___x_2839_ = lean_array_push(v_vs_2819_, v_x_2817_);
v___x_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
return v___x_2840_;
}
else
{
lean_object* v_expr_2841_; uint64_t v_configKey_2842_; lean_object* v_k_x27_2843_; lean_object* v_expr_2844_; uint64_t v_configKey_2845_; uint8_t v___x_2846_; 
v_expr_2841_ = lean_ctor_get(v_x_2816_, 0);
v_configKey_2842_ = lean_ctor_get_uint64(v_x_2816_, sizeof(void*)*1);
v_k_x27_2843_ = lean_array_fget_borrowed(v_ks_2818_, v_x_2815_);
v_expr_2844_ = lean_ctor_get(v_k_x27_2843_, 0);
v_configKey_2845_ = lean_ctor_get_uint64(v_k_x27_2843_, sizeof(void*)*1);
v___x_2846_ = lean_expr_equal(v_expr_2841_, v_expr_2844_);
if (v___x_2846_ == 0)
{
v___y_2824_ = v___x_2846_;
goto v___jp_2823_;
}
else
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_uint64_dec_eq(v_configKey_2842_, v_configKey_2845_);
v___y_2824_ = v___x_2847_;
goto v___jp_2823_;
}
}
v___jp_2823_:
{
if (v___y_2824_ == 0)
{
lean_object* v___x_2826_; 
if (v_isShared_2822_ == 0)
{
v___x_2826_ = v___x_2821_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_ks_2818_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_vs_2819_);
v___x_2826_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_x_2815_, v___x_2827_);
lean_dec(v_x_2815_);
v_x_2814_ = v___x_2826_;
v_x_2815_ = v___x_2828_;
goto _start;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2831_ = lean_array_fset(v_ks_2818_, v_x_2815_, v_x_2816_);
v___x_2832_ = lean_array_fset(v_vs_2819_, v_x_2815_, v_x_2817_);
lean_dec(v_x_2815_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2832_);
lean_ctor_set(v___x_2821_, 0, v___x_2831_);
v___x_2834_ = v___x_2821_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2849_, lean_object* v_k_2850_, lean_object* v_v_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2849_, v___x_2852_, v_k_2850_, v_v_2851_);
return v___x_2853_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2855_, size_t v_x_2856_, size_t v_x_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2855_) == 0)
{
lean_object* v_es_2860_; size_t v___x_2861_; size_t v___x_2862_; lean_object* v_j_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_es_2860_ = lean_ctor_get(v_x_2855_, 0);
v___x_2861_ = ((size_t)31ULL);
v___x_2862_ = lean_usize_land(v_x_2856_, v___x_2861_);
v_j_2863_ = lean_usize_to_nat(v___x_2862_);
v___x_2864_ = lean_array_get_size(v_es_2860_);
v___x_2865_ = lean_nat_dec_lt(v_j_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_dec(v_j_2863_);
lean_dec(v_x_2859_);
lean_dec_ref(v_x_2858_);
return v_x_2855_;
}
else
{
lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2911_; 
lean_inc_ref(v_es_2860_);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v_x_2855_, 0);
lean_dec(v_unused_2912_);
v___x_2867_ = v_x_2855_;
v_isShared_2868_ = v_isSharedCheck_2911_;
goto v_resetjp_2866_;
}
else
{
lean_dec(v_x_2855_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2911_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v_v_2869_; lean_object* v___x_2870_; lean_object* v_xs_x27_2871_; lean_object* v___y_2873_; 
v_v_2869_ = lean_array_fget(v_es_2860_, v_j_2863_);
v___x_2870_ = lean_box(0);
v_xs_x27_2871_ = lean_array_fset(v_es_2860_, v_j_2863_, v___x_2870_);
switch(lean_obj_tag(v_v_2869_))
{
case 0:
{
lean_object* v_key_2878_; lean_object* v_val_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2896_; 
v_key_2878_ = lean_ctor_get(v_v_2869_, 0);
v_val_2879_ = lean_ctor_get(v_v_2869_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_v_2869_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2881_ = v_v_2869_;
v_isShared_2882_ = v_isSharedCheck_2896_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_val_2879_);
lean_inc(v_key_2878_);
lean_dec(v_v_2869_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2896_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___y_2884_; lean_object* v_expr_2890_; uint64_t v_configKey_2891_; lean_object* v_expr_2892_; uint64_t v_configKey_2893_; uint8_t v___x_2894_; 
v_expr_2890_ = lean_ctor_get(v_x_2858_, 0);
v_configKey_2891_ = lean_ctor_get_uint64(v_x_2858_, sizeof(void*)*1);
v_expr_2892_ = lean_ctor_get(v_key_2878_, 0);
v_configKey_2893_ = lean_ctor_get_uint64(v_key_2878_, sizeof(void*)*1);
v___x_2894_ = lean_expr_equal(v_expr_2890_, v_expr_2892_);
if (v___x_2894_ == 0)
{
v___y_2884_ = v___x_2894_;
goto v___jp_2883_;
}
else
{
uint8_t v___x_2895_; 
v___x_2895_ = lean_uint64_dec_eq(v_configKey_2891_, v_configKey_2893_);
v___y_2884_ = v___x_2895_;
goto v___jp_2883_;
}
v___jp_2883_:
{
if (v___y_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_del_object(v___x_2881_);
v___x_2885_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2878_, v_val_2879_, v_x_2858_, v_x_2859_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v___y_2873_ = v___x_2886_;
goto v___jp_2872_;
}
else
{
lean_object* v___x_2888_; 
lean_dec(v_val_2879_);
lean_dec(v_key_2878_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v_x_2859_);
lean_ctor_set(v___x_2881_, 0, v_x_2858_);
v___x_2888_ = v___x_2881_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_x_2858_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_x_2859_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
v___y_2873_ = v___x_2888_;
goto v___jp_2872_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2909_; 
v_node_2897_ = lean_ctor_get(v_v_2869_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_v_2869_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2899_ = v_v_2869_;
v_isShared_2900_ = v_isSharedCheck_2909_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_node_2897_);
lean_dec(v_v_2869_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2909_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2901_ = ((size_t)5ULL);
v___x_2902_ = lean_usize_shift_right(v_x_2856_, v___x_2901_);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_x_2857_, v___x_2903_);
v___x_2905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2897_, v___x_2902_, v___x_2904_, v_x_2858_, v_x_2859_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2905_);
v___x_2907_ = v___x_2899_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v___y_2873_ = v___x_2907_;
goto v___jp_2872_;
}
}
}
default: 
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_x_2858_);
lean_ctor_set(v___x_2910_, 1, v_x_2859_);
v___y_2873_ = v___x_2910_;
goto v___jp_2872_;
}
}
v___jp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = lean_array_fset(v_xs_x27_2871_, v_j_2863_, v___y_2873_);
lean_dec(v_j_2863_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2874_);
v___x_2876_ = v___x_2867_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
else
{
lean_object* v_ks_2913_; lean_object* v_vs_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2932_; 
v_ks_2913_ = lean_ctor_get(v_x_2855_, 0);
v_vs_2914_ = lean_ctor_get(v_x_2855_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2916_ = v_x_2855_;
v_isShared_2917_ = v_isSharedCheck_2932_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_vs_2914_);
lean_inc(v_ks_2913_);
lean_dec(v_x_2855_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2932_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_ks_2913_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_vs_2914_);
v___x_2919_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v_newNode_2920_; size_t v___x_2921_; uint8_t v___x_2922_; 
v_newNode_2920_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2919_, v_x_2858_, v_x_2859_);
v___x_2921_ = ((size_t)7ULL);
v___x_2922_ = lean_usize_dec_le(v___x_2921_, v_x_2857_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2920_);
v___x_2924_ = lean_unsigned_to_nat(4u);
v___x_2925_ = lean_nat_dec_lt(v___x_2923_, v___x_2924_);
lean_dec(v___x_2923_);
if (v___x_2925_ == 0)
{
lean_object* v_ks_2926_; lean_object* v_vs_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_ks_2926_ = lean_ctor_get(v_newNode_2920_, 0);
lean_inc_ref(v_ks_2926_);
v_vs_2927_ = lean_ctor_get(v_newNode_2920_, 1);
lean_inc_ref(v_vs_2927_);
lean_dec_ref(v_newNode_2920_);
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2857_, v_ks_2926_, v_vs_2927_, v___x_2928_, v___x_2929_);
lean_dec_ref(v_vs_2927_);
lean_dec_ref(v_ks_2926_);
return v___x_2930_;
}
else
{
return v_newNode_2920_;
}
}
else
{
return v_newNode_2920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2933_, lean_object* v_keys_2934_, lean_object* v_vals_2935_, lean_object* v_i_2936_, lean_object* v_entries_2937_){
_start:
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = lean_array_get_size(v_keys_2934_);
v___x_2939_ = lean_nat_dec_lt(v_i_2936_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_dec(v_i_2936_);
return v_entries_2937_;
}
else
{
lean_object* v_k_2940_; lean_object* v_expr_2941_; uint64_t v_configKey_2942_; lean_object* v_v_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; size_t v_h_2946_; size_t v___x_2947_; lean_object* v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v_h_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_k_2940_ = lean_array_fget_borrowed(v_keys_2934_, v_i_2936_);
v_expr_2941_ = lean_ctor_get(v_k_2940_, 0);
v_configKey_2942_ = lean_ctor_get_uint64(v_k_2940_, sizeof(void*)*1);
v_v_2943_ = lean_array_fget_borrowed(v_vals_2935_, v_i_2936_);
v___x_2944_ = l_Lean_Expr_hash(v_expr_2941_);
v___x_2945_ = lean_uint64_mix_hash(v___x_2944_, v_configKey_2942_);
v_h_2946_ = lean_uint64_to_usize(v___x_2945_);
v___x_2947_ = ((size_t)5ULL);
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_sub(v_depth_2933_, v___x_2949_);
v___x_2951_ = lean_usize_mul(v___x_2947_, v___x_2950_);
v_h_2952_ = lean_usize_shift_right(v_h_2946_, v___x_2951_);
v___x_2953_ = lean_nat_add(v_i_2936_, v___x_2948_);
lean_dec(v_i_2936_);
lean_inc(v_v_2943_);
lean_inc(v_k_2940_);
v___x_2954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2937_, v_h_2952_, v_depth_2933_, v_k_2940_, v_v_2943_);
v_i_2936_ = v___x_2953_;
v_entries_2937_ = v___x_2954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2956_, lean_object* v_keys_2957_, lean_object* v_vals_2958_, lean_object* v_i_2959_, lean_object* v_entries_2960_){
_start:
{
size_t v_depth_boxed_2961_; lean_object* v_res_2962_; 
v_depth_boxed_2961_ = lean_unbox_usize(v_depth_2956_);
lean_dec(v_depth_2956_);
v_res_2962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2961_, v_keys_2957_, v_vals_2958_, v_i_2959_, v_entries_2960_);
lean_dec_ref(v_vals_2958_);
lean_dec_ref(v_keys_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_){
_start:
{
size_t v_x_2785__boxed_2968_; size_t v_x_2786__boxed_2969_; lean_object* v_res_2970_; 
v_x_2785__boxed_2968_ = lean_unbox_usize(v_x_2964_);
lean_dec(v_x_2964_);
v_x_2786__boxed_2969_ = lean_unbox_usize(v_x_2965_);
lean_dec(v_x_2965_);
v_res_2970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2963_, v_x_2785__boxed_2968_, v_x_2786__boxed_2969_, v_x_2966_, v_x_2967_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_){
_start:
{
lean_object* v_expr_2974_; uint64_t v_configKey_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; lean_object* v___x_2980_; 
v_expr_2974_ = lean_ctor_get(v_x_2972_, 0);
v_configKey_2975_ = lean_ctor_get_uint64(v_x_2972_, sizeof(void*)*1);
v___x_2976_ = l_Lean_Expr_hash(v_expr_2974_);
v___x_2977_ = lean_uint64_mix_hash(v___x_2976_, v_configKey_2975_);
v___x_2978_ = lean_uint64_to_usize(v___x_2977_);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2971_, v___x_2978_, v___x_2979_, v_x_2972_, v_x_2973_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2981_, lean_object* v_vals_2982_, lean_object* v_i_2983_, lean_object* v_k_2984_){
_start:
{
uint8_t v___y_2986_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = lean_array_get_size(v_keys_2981_);
v___x_2993_ = lean_nat_dec_lt(v_i_2983_, v___x_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; 
lean_dec(v_i_2983_);
v___x_2994_ = lean_box(0);
return v___x_2994_;
}
else
{
lean_object* v_expr_2995_; uint64_t v_configKey_2996_; lean_object* v_k_x27_2997_; lean_object* v_expr_2998_; uint64_t v_configKey_2999_; uint8_t v___x_3000_; 
v_expr_2995_ = lean_ctor_get(v_k_2984_, 0);
v_configKey_2996_ = lean_ctor_get_uint64(v_k_2984_, sizeof(void*)*1);
v_k_x27_2997_ = lean_array_fget_borrowed(v_keys_2981_, v_i_2983_);
v_expr_2998_ = lean_ctor_get(v_k_x27_2997_, 0);
v_configKey_2999_ = lean_ctor_get_uint64(v_k_x27_2997_, sizeof(void*)*1);
v___x_3000_ = lean_expr_equal(v_expr_2995_, v_expr_2998_);
if (v___x_3000_ == 0)
{
v___y_2986_ = v___x_3000_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_uint64_dec_eq(v_configKey_2996_, v_configKey_2999_);
v___y_2986_ = v___x_3001_;
goto v___jp_2985_;
}
}
v___jp_2985_:
{
if (v___y_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_nat_add(v_i_2983_, v___x_2987_);
lean_dec(v_i_2983_);
v_i_2983_ = v___x_2988_;
goto _start;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_array_fget_borrowed(v_vals_2982_, v_i_2983_);
lean_dec(v_i_2983_);
lean_inc(v___x_2990_);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3002_, lean_object* v_vals_3003_, lean_object* v_i_3004_, lean_object* v_k_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3002_, v_vals_3003_, v_i_3004_, v_k_3005_);
lean_dec_ref(v_k_3005_);
lean_dec_ref(v_vals_3003_);
lean_dec_ref(v_keys_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3007_, size_t v_x_3008_, lean_object* v_x_3009_){
_start:
{
if (lean_obj_tag(v_x_3007_) == 0)
{
lean_object* v_es_3010_; lean_object* v___x_3011_; size_t v___x_3012_; size_t v___x_3013_; lean_object* v_j_3014_; lean_object* v___x_3015_; 
v_es_3010_ = lean_ctor_get(v_x_3007_, 0);
v___x_3011_ = lean_box(2);
v___x_3012_ = ((size_t)31ULL);
v___x_3013_ = lean_usize_land(v_x_3008_, v___x_3012_);
v_j_3014_ = lean_usize_to_nat(v___x_3013_);
v___x_3015_ = lean_array_get_borrowed(v___x_3011_, v_es_3010_, v_j_3014_);
lean_dec(v_j_3014_);
switch(lean_obj_tag(v___x_3015_))
{
case 0:
{
lean_object* v_key_3016_; lean_object* v_val_3017_; uint8_t v___y_3019_; lean_object* v_expr_3022_; uint64_t v_configKey_3023_; lean_object* v_expr_3024_; uint64_t v_configKey_3025_; uint8_t v___x_3026_; 
v_key_3016_ = lean_ctor_get(v___x_3015_, 0);
v_val_3017_ = lean_ctor_get(v___x_3015_, 1);
v_expr_3022_ = lean_ctor_get(v_x_3009_, 0);
v_configKey_3023_ = lean_ctor_get_uint64(v_x_3009_, sizeof(void*)*1);
v_expr_3024_ = lean_ctor_get(v_key_3016_, 0);
v_configKey_3025_ = lean_ctor_get_uint64(v_key_3016_, sizeof(void*)*1);
v___x_3026_ = lean_expr_equal(v_expr_3022_, v_expr_3024_);
if (v___x_3026_ == 0)
{
v___y_3019_ = v___x_3026_;
goto v___jp_3018_;
}
else
{
uint8_t v___x_3027_; 
v___x_3027_ = lean_uint64_dec_eq(v_configKey_3023_, v_configKey_3025_);
v___y_3019_ = v___x_3027_;
goto v___jp_3018_;
}
v___jp_3018_:
{
if (v___y_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_box(0);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_inc(v_val_3017_);
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_val_3017_);
return v___x_3021_;
}
}
}
case 1:
{
lean_object* v_node_3028_; size_t v___x_3029_; size_t v___x_3030_; 
v_node_3028_ = lean_ctor_get(v___x_3015_, 0);
v___x_3029_ = ((size_t)5ULL);
v___x_3030_ = lean_usize_shift_right(v_x_3008_, v___x_3029_);
v_x_3007_ = v_node_3028_;
v_x_3008_ = v___x_3030_;
goto _start;
}
default: 
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_box(0);
return v___x_3032_;
}
}
}
else
{
lean_object* v_ks_3033_; lean_object* v_vs_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_ks_3033_ = lean_ctor_get(v_x_3007_, 0);
v_vs_3034_ = lean_ctor_get(v_x_3007_, 1);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3033_, v_vs_3034_, v___x_3035_, v_x_3009_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_){
_start:
{
size_t v_x_2990__boxed_3040_; lean_object* v_res_3041_; 
v_x_2990__boxed_3040_ = lean_unbox_usize(v_x_3038_);
lean_dec(v_x_3038_);
v_res_3041_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3037_, v_x_2990__boxed_3040_, v_x_3039_);
lean_dec_ref(v_x_3039_);
lean_dec_ref(v_x_3037_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_expr_3044_; uint64_t v_configKey_3045_; uint64_t v___x_3046_; uint64_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v_expr_3044_ = lean_ctor_get(v_x_3043_, 0);
v_configKey_3045_ = lean_ctor_get_uint64(v_x_3043_, sizeof(void*)*1);
v___x_3046_ = l_Lean_Expr_hash(v_expr_3044_);
v___x_3047_ = lean_uint64_mix_hash(v___x_3046_, v_configKey_3045_);
v___x_3048_ = lean_uint64_to_usize(v___x_3047_);
v___x_3049_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3042_, v___x_3048_, v_x_3043_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3050_, v_x_3051_);
lean_dec_ref(v_x_3051_);
lean_dec_ref(v_x_3050_);
return v_res_3052_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
switch(lean_obj_tag(v_e_3056_))
{
case 0:
{
lean_object* v_deBruijnIndex_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_deBruijnIndex_3094_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_deBruijnIndex_3094_);
lean_dec_ref_known(v_e_3056_, 1);
v___x_3095_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3096_ = l_Lean_mkBVar(v_deBruijnIndex_3094_);
v___x_3097_ = l_Lean_MessageData_ofExpr(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3095_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3098_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3099_;
}
case 1:
{
lean_object* v_fvarId_3100_; lean_object* v___x_3101_; 
v_fvarId_3100_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_fvarId_3100_);
lean_dec_ref_known(v_e_3056_, 1);
v___x_3101_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3100_, v_a_3057_, v_a_3059_, v_a_3060_);
return v___x_3101_;
}
case 2:
{
lean_object* v_mvarId_3102_; lean_object* v___x_3103_; 
v_mvarId_3102_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_mvarId_3102_);
lean_dec_ref_known(v_e_3056_, 1);
v___x_3103_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3102_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3103_;
}
case 3:
{
lean_object* v_u_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_u_3104_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_u_3104_);
lean_dec_ref_known(v_e_3056_, 1);
v___x_3105_ = l_Lean_Level_succ___override(v_u_3104_);
v___x_3106_ = l_Lean_mkSort(v___x_3105_);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
case 4:
{
lean_object* v_declName_3108_; lean_object* v_us_3109_; 
v_declName_3108_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_declName_3108_);
v_us_3109_ = lean_ctor_get(v_e_3056_, 1);
lean_inc(v_us_3109_);
if (lean_obj_tag(v_us_3109_) == 0)
{
lean_object* v___x_3126_; 
lean_dec_ref_known(v_e_3056_, 2);
v___x_3126_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3108_, v_us_3109_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3126_;
}
else
{
uint8_t v_cacheInferType_3127_; 
v_cacheInferType_3127_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3127_ == 0)
{
lean_dec_ref_known(v_e_3056_, 2);
goto v___jp_3110_;
}
else
{
uint8_t v___x_3128_; 
v___x_3128_ = l_Lean_Expr_hasMVar(v_e_3056_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3195_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3195_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3195_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3174_; lean_object* v_cache_3175_; lean_object* v_inferType_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_st_ref_get(v_a_3058_);
v_cache_3175_ = lean_ctor_get(v___x_3174_, 1);
lean_inc_ref(v_cache_3175_);
lean_dec(v___x_3174_);
v_inferType_3176_ = lean_ctor_get(v_cache_3175_, 0);
lean_inc_ref(v_inferType_3176_);
lean_dec_ref(v_cache_3175_);
v___x_3177_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3176_, v_a_3130_);
lean_dec_ref(v_inferType_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_toCold_3178_; lean_object* v_cancelTk_x3f_3179_; 
lean_del_object(v___x_3132_);
v_toCold_3178_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3179_ = lean_ctor_get(v_toCold_3178_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3179_) == 1)
{
lean_object* v_val_3180_; uint8_t v___x_3181_; 
v_val_3180_ = lean_ctor_get(v_cancelTk_x3f_3179_, 0);
v___x_3181_ = l_IO_CancelToken_isSet(v_val_3180_);
if (v___x_3181_ == 0)
{
goto v___jp_3134_;
}
else
{
lean_object* v___x_3182_; lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_a_3130_);
lean_dec(v_us_3109_);
lean_dec(v_declName_3108_);
v___x_3182_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
goto v___jp_3134_;
}
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3193_; 
lean_dec(v_a_3130_);
lean_dec(v_us_3109_);
lean_dec(v_declName_3108_);
v_val_3191_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v___x_3177_, 1);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v_val_3191_);
v___x_3193_ = v___x_3132_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_val_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
v___jp_3134_:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3108_, v_us_3109_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; uint8_t v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
v___x_3137_ = l_Lean_Expr_hasMVar(v_a_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3172_; 
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_3135_, 0);
lean_dec(v_unused_3173_);
v___x_3139_ = v___x_3135_;
v_isShared_3140_ = v_isSharedCheck_3172_;
goto v_resetjp_3138_;
}
else
{
lean_dec(v___x_3135_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3172_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v_cache_3142_; lean_object* v_mctx_3143_; lean_object* v_zetaDeltaFVarIds_3144_; lean_object* v_postponed_3145_; lean_object* v_diag_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3171_; 
v___x_3141_ = lean_st_ref_take(v_a_3058_);
v_cache_3142_ = lean_ctor_get(v___x_3141_, 1);
v_mctx_3143_ = lean_ctor_get(v___x_3141_, 0);
v_zetaDeltaFVarIds_3144_ = lean_ctor_get(v___x_3141_, 2);
v_postponed_3145_ = lean_ctor_get(v___x_3141_, 3);
v_diag_3146_ = lean_ctor_get(v___x_3141_, 4);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3148_ = v___x_3141_;
v_isShared_3149_ = v_isSharedCheck_3171_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_diag_3146_);
lean_inc(v_postponed_3145_);
lean_inc(v_zetaDeltaFVarIds_3144_);
lean_inc(v_cache_3142_);
lean_inc(v_mctx_3143_);
lean_dec(v___x_3141_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3171_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_inferType_3150_; lean_object* v_funInfo_3151_; lean_object* v_synthInstance_3152_; lean_object* v_whnf_3153_; lean_object* v_defEqTrans_3154_; lean_object* v_defEqPerm_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3170_; 
v_inferType_3150_ = lean_ctor_get(v_cache_3142_, 0);
v_funInfo_3151_ = lean_ctor_get(v_cache_3142_, 1);
v_synthInstance_3152_ = lean_ctor_get(v_cache_3142_, 2);
v_whnf_3153_ = lean_ctor_get(v_cache_3142_, 3);
v_defEqTrans_3154_ = lean_ctor_get(v_cache_3142_, 4);
v_defEqPerm_3155_ = lean_ctor_get(v_cache_3142_, 5);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_cache_3142_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3157_ = v_cache_3142_;
v_isShared_3158_ = v_isSharedCheck_3170_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_defEqPerm_3155_);
lean_inc(v_defEqTrans_3154_);
lean_inc(v_whnf_3153_);
lean_inc(v_synthInstance_3152_);
lean_inc(v_funInfo_3151_);
lean_inc(v_inferType_3150_);
lean_dec(v_cache_3142_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3170_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
lean_inc(v_a_3136_);
v___x_3159_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3150_, v_a_3130_, v_a_3136_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_funInfo_3151_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_synthInstance_3152_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_whnf_3153_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_defEqTrans_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 5, v_defEqPerm_3155_);
v___x_3161_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3163_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v___x_3161_);
v___x_3163_ = v___x_3148_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_mctx_3143_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_zetaDeltaFVarIds_3144_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_postponed_3145_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v_diag_3146_);
v___x_3163_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_st_ref_put(v_a_3058_, v___x_3163_);
if (v_isShared_3140_ == 0)
{
v___x_3166_ = v___x_3139_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3136_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3136_);
lean_dec(v_a_3130_);
return v___x_3135_;
}
}
else
{
lean_dec(v_a_3130_);
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_us_3109_);
lean_dec(v_declName_3108_);
v_a_3196_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3129_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3129_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3056_, 2);
goto v___jp_3110_;
}
}
}
v___jp_3110_:
{
lean_object* v_toCold_3111_; lean_object* v_cancelTk_x3f_3112_; 
v_toCold_3111_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3112_ = lean_ctor_get(v_toCold_3111_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3112_) == 1)
{
lean_object* v_val_3113_; uint8_t v___x_3114_; 
v_val_3113_ = lean_ctor_get(v_cancelTk_x3f_3112_, 0);
v___x_3114_ = l_IO_CancelToken_isSet(v_val_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3108_, v_us_3109_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3115_;
}
else
{
lean_object* v___x_3116_; lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_us_3109_);
lean_dec(v_declName_3108_);
v___x_3116_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3108_, v_us_3109_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3125_;
}
}
}
case 5:
{
lean_object* v_fn_3204_; uint8_t v_cacheInferType_3205_; lean_object* v_nargs_3206_; lean_object* v___x_3207_; lean_object* v_dummy_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_fn_3204_ = lean_ctor_get(v_e_3056_, 0);
v_cacheInferType_3205_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*7 + 3);
v_nargs_3206_ = l_Lean_Expr_getAppNumArgs(v_e_3056_);
v___x_3207_ = l_Lean_Expr_getAppFn(v_fn_3204_);
v_dummy_3208_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3206_);
v___x_3209_ = lean_mk_array(v_nargs_3206_, v_dummy_3208_);
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_sub(v_nargs_3206_, v___x_3210_);
lean_dec(v_nargs_3206_);
lean_inc_ref(v_e_3056_);
v___x_3212_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3056_, v___x_3209_, v___x_3211_);
if (v_cacheInferType_3205_ == 0)
{
lean_dec_ref_known(v_e_3056_, 2);
goto v___jp_3213_;
}
else
{
uint8_t v___x_3229_; 
v___x_3229_ = l_Lean_Expr_hasMVar(v_e_3056_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3296_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3233_ = v___x_3230_;
v_isShared_3234_ = v_isSharedCheck_3296_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3230_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3296_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3275_; lean_object* v_cache_3276_; lean_object* v_inferType_3277_; lean_object* v___x_3278_; 
v___x_3275_ = lean_st_ref_get(v_a_3058_);
v_cache_3276_ = lean_ctor_get(v___x_3275_, 1);
lean_inc_ref(v_cache_3276_);
lean_dec(v___x_3275_);
v_inferType_3277_ = lean_ctor_get(v_cache_3276_, 0);
lean_inc_ref(v_inferType_3277_);
lean_dec_ref(v_cache_3276_);
v___x_3278_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3277_, v_a_3231_);
lean_dec_ref(v_inferType_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_toCold_3279_; lean_object* v_cancelTk_x3f_3280_; 
lean_del_object(v___x_3233_);
v_toCold_3279_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3280_ = lean_ctor_get(v_toCold_3279_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3280_) == 1)
{
lean_object* v_val_3281_; uint8_t v___x_3282_; 
v_val_3281_ = lean_ctor_get(v_cancelTk_x3f_3280_, 0);
v___x_3282_ = l_IO_CancelToken_isSet(v_val_3281_);
if (v___x_3282_ == 0)
{
goto v___jp_3235_;
}
else
{
lean_object* v___x_3283_; lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_a_3231_);
lean_dec_ref(v___x_3212_);
lean_dec_ref(v___x_3207_);
v___x_3283_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
goto v___jp_3235_;
}
}
else
{
lean_object* v_val_3292_; lean_object* v___x_3294_; 
lean_dec(v_a_3231_);
lean_dec_ref(v___x_3212_);
lean_dec_ref(v___x_3207_);
v_val_3292_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v___x_3278_, 1);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v_val_3292_);
v___x_3294_ = v___x_3233_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_val_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
v___jp_3235_:
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3207_, v___x_3212_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec_ref(v___x_3212_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; uint8_t v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
v___x_3238_ = l_Lean_Expr_hasMVar(v_a_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3273_; 
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; 
v_unused_3274_ = lean_ctor_get(v___x_3236_, 0);
lean_dec(v_unused_3274_);
v___x_3240_ = v___x_3236_;
v_isShared_3241_ = v_isSharedCheck_3273_;
goto v_resetjp_3239_;
}
else
{
lean_dec(v___x_3236_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3273_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v_cache_3243_; lean_object* v_mctx_3244_; lean_object* v_zetaDeltaFVarIds_3245_; lean_object* v_postponed_3246_; lean_object* v_diag_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3272_; 
v___x_3242_ = lean_st_ref_take(v_a_3058_);
v_cache_3243_ = lean_ctor_get(v___x_3242_, 1);
v_mctx_3244_ = lean_ctor_get(v___x_3242_, 0);
v_zetaDeltaFVarIds_3245_ = lean_ctor_get(v___x_3242_, 2);
v_postponed_3246_ = lean_ctor_get(v___x_3242_, 3);
v_diag_3247_ = lean_ctor_get(v___x_3242_, 4);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3249_ = v___x_3242_;
v_isShared_3250_ = v_isSharedCheck_3272_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_diag_3247_);
lean_inc(v_postponed_3246_);
lean_inc(v_zetaDeltaFVarIds_3245_);
lean_inc(v_cache_3243_);
lean_inc(v_mctx_3244_);
lean_dec(v___x_3242_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3272_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v_inferType_3251_; lean_object* v_funInfo_3252_; lean_object* v_synthInstance_3253_; lean_object* v_whnf_3254_; lean_object* v_defEqTrans_3255_; lean_object* v_defEqPerm_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3271_; 
v_inferType_3251_ = lean_ctor_get(v_cache_3243_, 0);
v_funInfo_3252_ = lean_ctor_get(v_cache_3243_, 1);
v_synthInstance_3253_ = lean_ctor_get(v_cache_3243_, 2);
v_whnf_3254_ = lean_ctor_get(v_cache_3243_, 3);
v_defEqTrans_3255_ = lean_ctor_get(v_cache_3243_, 4);
v_defEqPerm_3256_ = lean_ctor_get(v_cache_3243_, 5);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_cache_3243_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3258_ = v_cache_3243_;
v_isShared_3259_ = v_isSharedCheck_3271_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_defEqPerm_3256_);
lean_inc(v_defEqTrans_3255_);
lean_inc(v_whnf_3254_);
lean_inc(v_synthInstance_3253_);
lean_inc(v_funInfo_3252_);
lean_inc(v_inferType_3251_);
lean_dec(v_cache_3243_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3271_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_inc(v_a_3237_);
v___x_3260_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3251_, v_a_3231_, v_a_3237_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v___x_3260_);
v___x_3262_ = v___x_3258_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_funInfo_3252_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v_synthInstance_3253_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v_whnf_3254_);
lean_ctor_set(v_reuseFailAlloc_3270_, 4, v_defEqTrans_3255_);
lean_ctor_set(v_reuseFailAlloc_3270_, 5, v_defEqPerm_3256_);
v___x_3262_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3264_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3262_);
v___x_3264_ = v___x_3249_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_mctx_3244_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v_zetaDeltaFVarIds_3245_);
lean_ctor_set(v_reuseFailAlloc_3269_, 3, v_postponed_3246_);
lean_ctor_set(v_reuseFailAlloc_3269_, 4, v_diag_3247_);
v___x_3264_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_st_ref_put(v_a_3058_, v___x_3264_);
if (v_isShared_3241_ == 0)
{
v___x_3267_ = v___x_3240_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3237_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3237_);
lean_dec(v_a_3231_);
return v___x_3236_;
}
}
else
{
lean_dec(v_a_3231_);
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec_ref(v___x_3212_);
lean_dec_ref(v___x_3207_);
v_a_3297_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3230_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3230_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3056_, 2);
goto v___jp_3213_;
}
}
v___jp_3213_:
{
lean_object* v_toCold_3214_; lean_object* v_cancelTk_x3f_3215_; 
v_toCold_3214_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3215_ = lean_ctor_get(v_toCold_3214_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3215_) == 1)
{
lean_object* v_val_3216_; uint8_t v___x_3217_; 
v_val_3216_ = lean_ctor_get(v_cancelTk_x3f_3215_, 0);
v___x_3217_ = l_IO_CancelToken_isSet(v_val_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
v___x_3218_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3207_, v___x_3212_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec_ref(v___x_3212_);
return v___x_3218_;
}
else
{
lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v___x_3212_);
lean_dec_ref(v___x_3207_);
v___x_3219_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3207_, v___x_3212_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec_ref(v___x_3212_);
return v___x_3228_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3305_; 
v_cacheInferType_3305_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3305_ == 0)
{
goto v___jp_3078_;
}
else
{
uint8_t v___x_3306_; 
v___x_3306_ = l_Lean_Expr_hasMVar(v_e_3056_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; 
lean_inc_ref(v_e_3056_);
v___x_3307_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3373_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3373_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3373_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3352_; lean_object* v_cache_3353_; lean_object* v_inferType_3354_; lean_object* v___x_3355_; 
v___x_3352_ = lean_st_ref_get(v_a_3058_);
v_cache_3353_ = lean_ctor_get(v___x_3352_, 1);
lean_inc_ref(v_cache_3353_);
lean_dec(v___x_3352_);
v_inferType_3354_ = lean_ctor_get(v_cache_3353_, 0);
lean_inc_ref(v_inferType_3354_);
lean_dec_ref(v_cache_3353_);
v___x_3355_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3354_, v_a_3308_);
lean_dec_ref(v_inferType_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_toCold_3356_; lean_object* v_cancelTk_x3f_3357_; 
lean_del_object(v___x_3310_);
v_toCold_3356_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3357_ = lean_ctor_get(v_toCold_3356_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3357_) == 1)
{
lean_object* v_val_3358_; uint8_t v___x_3359_; 
v_val_3358_ = lean_ctor_get(v_cancelTk_x3f_3357_, 0);
v___x_3359_ = l_IO_CancelToken_isSet(v_val_3358_);
if (v___x_3359_ == 0)
{
goto v___jp_3312_;
}
else
{
lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3308_);
lean_dec_ref_known(v_e_3056_, 3);
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
goto v___jp_3312_;
}
}
else
{
lean_object* v_val_3369_; lean_object* v___x_3371_; 
lean_dec(v_a_3308_);
lean_dec_ref_known(v_e_3056_, 3);
v_val_3369_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3355_, 1);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v_val_3369_);
v___x_3371_ = v___x_3310_;
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
v___jp_3312_:
{
lean_object* v___x_3313_; 
v___x_3313_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; uint8_t v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
v___x_3315_ = l_Lean_Expr_hasMVar(v_a_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3350_; 
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v___x_3313_, 0);
lean_dec(v_unused_3351_);
v___x_3317_ = v___x_3313_;
v_isShared_3318_ = v_isSharedCheck_3350_;
goto v_resetjp_3316_;
}
else
{
lean_dec(v___x_3313_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3350_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; lean_object* v_cache_3320_; lean_object* v_mctx_3321_; lean_object* v_zetaDeltaFVarIds_3322_; lean_object* v_postponed_3323_; lean_object* v_diag_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3349_; 
v___x_3319_ = lean_st_ref_take(v_a_3058_);
v_cache_3320_ = lean_ctor_get(v___x_3319_, 1);
v_mctx_3321_ = lean_ctor_get(v___x_3319_, 0);
v_zetaDeltaFVarIds_3322_ = lean_ctor_get(v___x_3319_, 2);
v_postponed_3323_ = lean_ctor_get(v___x_3319_, 3);
v_diag_3324_ = lean_ctor_get(v___x_3319_, 4);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3326_ = v___x_3319_;
v_isShared_3327_ = v_isSharedCheck_3349_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_diag_3324_);
lean_inc(v_postponed_3323_);
lean_inc(v_zetaDeltaFVarIds_3322_);
lean_inc(v_cache_3320_);
lean_inc(v_mctx_3321_);
lean_dec(v___x_3319_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3349_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v_inferType_3328_; lean_object* v_funInfo_3329_; lean_object* v_synthInstance_3330_; lean_object* v_whnf_3331_; lean_object* v_defEqTrans_3332_; lean_object* v_defEqPerm_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3348_; 
v_inferType_3328_ = lean_ctor_get(v_cache_3320_, 0);
v_funInfo_3329_ = lean_ctor_get(v_cache_3320_, 1);
v_synthInstance_3330_ = lean_ctor_get(v_cache_3320_, 2);
v_whnf_3331_ = lean_ctor_get(v_cache_3320_, 3);
v_defEqTrans_3332_ = lean_ctor_get(v_cache_3320_, 4);
v_defEqPerm_3333_ = lean_ctor_get(v_cache_3320_, 5);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_cache_3320_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3335_ = v_cache_3320_;
v_isShared_3336_ = v_isSharedCheck_3348_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_defEqPerm_3333_);
lean_inc(v_defEqTrans_3332_);
lean_inc(v_whnf_3331_);
lean_inc(v_synthInstance_3330_);
lean_inc(v_funInfo_3329_);
lean_inc(v_inferType_3328_);
lean_dec(v_cache_3320_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3348_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_inc(v_a_3314_);
v___x_3337_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3328_, v_a_3308_, v_a_3314_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_funInfo_3329_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_synthInstance_3330_);
lean_ctor_set(v_reuseFailAlloc_3347_, 3, v_whnf_3331_);
lean_ctor_set(v_reuseFailAlloc_3347_, 4, v_defEqTrans_3332_);
lean_ctor_set(v_reuseFailAlloc_3347_, 5, v_defEqPerm_3333_);
v___x_3339_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 1, v___x_3339_);
v___x_3341_ = v___x_3326_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_mctx_3321_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_zetaDeltaFVarIds_3322_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_postponed_3323_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_diag_3324_);
v___x_3341_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3342_ = lean_st_ref_put(v_a_3058_, v___x_3341_);
if (v_isShared_3318_ == 0)
{
v___x_3344_ = v___x_3317_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3314_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3314_);
lean_dec(v_a_3308_);
return v___x_3313_;
}
}
else
{
lean_dec(v_a_3308_);
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref_known(v_e_3056_, 3);
v_a_3374_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3307_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3307_);
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
goto v___jp_3078_;
}
}
}
case 9:
{
lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_a_3382_ = lean_ctor_get(v_e_3056_, 0);
lean_inc_ref(v_a_3382_);
lean_dec_ref_known(v_e_3056_, 1);
v___x_3383_ = l_Lean_Literal_type(v_a_3382_);
lean_dec_ref(v_a_3382_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
return v___x_3384_;
}
case 10:
{
lean_object* v_expr_3385_; 
v_expr_3385_ = lean_ctor_get(v_e_3056_, 1);
lean_inc_ref(v_expr_3385_);
lean_dec_ref_known(v_e_3056_, 2);
v_e_3056_ = v_expr_3385_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3387_; lean_object* v_idx_3388_; lean_object* v_struct_3389_; uint8_t v_cacheInferType_3406_; 
v_typeName_3387_ = lean_ctor_get(v_e_3056_, 0);
lean_inc(v_typeName_3387_);
v_idx_3388_ = lean_ctor_get(v_e_3056_, 1);
lean_inc(v_idx_3388_);
v_struct_3389_ = lean_ctor_get(v_e_3056_, 2);
lean_inc_ref(v_struct_3389_);
v_cacheInferType_3406_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3406_ == 0)
{
lean_dec_ref_known(v_e_3056_, 3);
goto v___jp_3390_;
}
else
{
uint8_t v___x_3407_; 
v___x_3407_ = l_Lean_Expr_hasMVar(v_e_3056_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3474_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3474_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3474_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3453_; lean_object* v_cache_3454_; lean_object* v_inferType_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_st_ref_get(v_a_3058_);
v_cache_3454_ = lean_ctor_get(v___x_3453_, 1);
lean_inc_ref(v_cache_3454_);
lean_dec(v___x_3453_);
v_inferType_3455_ = lean_ctor_get(v_cache_3454_, 0);
lean_inc_ref(v_inferType_3455_);
lean_dec_ref(v_cache_3454_);
v___x_3456_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3455_, v_a_3409_);
lean_dec_ref(v_inferType_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_toCold_3457_; lean_object* v_cancelTk_x3f_3458_; 
lean_del_object(v___x_3411_);
v_toCold_3457_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3458_ = lean_ctor_get(v_toCold_3457_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3458_) == 1)
{
lean_object* v_val_3459_; uint8_t v___x_3460_; 
v_val_3459_ = lean_ctor_get(v_cancelTk_x3f_3458_, 0);
v___x_3460_ = l_IO_CancelToken_isSet(v_val_3459_);
if (v___x_3460_ == 0)
{
goto v___jp_3413_;
}
else
{
lean_object* v___x_3461_; lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec(v_a_3409_);
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v___x_3461_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
goto v___jp_3413_;
}
}
else
{
lean_object* v_val_3470_; lean_object* v___x_3472_; 
lean_dec(v_a_3409_);
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v_val_3470_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_val_3470_);
lean_dec_ref_known(v___x_3456_, 1);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v_val_3470_);
v___x_3472_ = v___x_3411_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_val_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
v___jp_3413_:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; uint8_t v___x_3416_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
v___x_3416_ = l_Lean_Expr_hasMVar(v_a_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3451_; 
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v___x_3414_, 0);
lean_dec(v_unused_3452_);
v___x_3418_ = v___x_3414_;
v_isShared_3419_ = v_isSharedCheck_3451_;
goto v_resetjp_3417_;
}
else
{
lean_dec(v___x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3451_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v_cache_3421_; lean_object* v_mctx_3422_; lean_object* v_zetaDeltaFVarIds_3423_; lean_object* v_postponed_3424_; lean_object* v_diag_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3450_; 
v___x_3420_ = lean_st_ref_take(v_a_3058_);
v_cache_3421_ = lean_ctor_get(v___x_3420_, 1);
v_mctx_3422_ = lean_ctor_get(v___x_3420_, 0);
v_zetaDeltaFVarIds_3423_ = lean_ctor_get(v___x_3420_, 2);
v_postponed_3424_ = lean_ctor_get(v___x_3420_, 3);
v_diag_3425_ = lean_ctor_get(v___x_3420_, 4);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3427_ = v___x_3420_;
v_isShared_3428_ = v_isSharedCheck_3450_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_diag_3425_);
lean_inc(v_postponed_3424_);
lean_inc(v_zetaDeltaFVarIds_3423_);
lean_inc(v_cache_3421_);
lean_inc(v_mctx_3422_);
lean_dec(v___x_3420_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3450_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_inferType_3429_; lean_object* v_funInfo_3430_; lean_object* v_synthInstance_3431_; lean_object* v_whnf_3432_; lean_object* v_defEqTrans_3433_; lean_object* v_defEqPerm_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3449_; 
v_inferType_3429_ = lean_ctor_get(v_cache_3421_, 0);
v_funInfo_3430_ = lean_ctor_get(v_cache_3421_, 1);
v_synthInstance_3431_ = lean_ctor_get(v_cache_3421_, 2);
v_whnf_3432_ = lean_ctor_get(v_cache_3421_, 3);
v_defEqTrans_3433_ = lean_ctor_get(v_cache_3421_, 4);
v_defEqPerm_3434_ = lean_ctor_get(v_cache_3421_, 5);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_cache_3421_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3436_ = v_cache_3421_;
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_defEqPerm_3434_);
lean_inc(v_defEqTrans_3433_);
lean_inc(v_whnf_3432_);
lean_inc(v_synthInstance_3431_);
lean_inc(v_funInfo_3430_);
lean_inc(v_inferType_3429_);
lean_dec(v_cache_3421_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3449_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
lean_inc(v_a_3415_);
v___x_3438_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3429_, v_a_3409_, v_a_3415_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_funInfo_3430_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_synthInstance_3431_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_whnf_3432_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_defEqTrans_3433_);
lean_ctor_set(v_reuseFailAlloc_3448_, 5, v_defEqPerm_3434_);
v___x_3440_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3440_);
v___x_3442_ = v___x_3427_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_mctx_3422_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_zetaDeltaFVarIds_3423_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_postponed_3424_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_diag_3425_);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_st_ref_put(v_a_3058_, v___x_3442_);
if (v_isShared_3419_ == 0)
{
v___x_3445_ = v___x_3418_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3415_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3415_);
lean_dec(v_a_3409_);
return v___x_3414_;
}
}
else
{
lean_dec(v_a_3409_);
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v_a_3475_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3408_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3408_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3056_, 3);
goto v___jp_3390_;
}
}
v___jp_3390_:
{
lean_object* v_toCold_3391_; lean_object* v_cancelTk_x3f_3392_; 
v_toCold_3391_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3392_ = lean_ctor_get(v_toCold_3391_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3392_) == 1)
{
lean_object* v_val_3393_; uint8_t v___x_3394_; 
v_val_3393_ = lean_ctor_get(v_cancelTk_x3f_3392_, 0);
v___x_3394_ = l_IO_CancelToken_isSet(v_val_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec_ref(v_struct_3389_);
lean_dec(v_idx_3388_);
lean_dec(v_typeName_3387_);
v___x_3396_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3387_, v_idx_3388_, v_struct_3389_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3405_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3483_; 
v_cacheInferType_3483_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3483_ == 0)
{
goto v___jp_3062_;
}
else
{
uint8_t v___x_3484_; 
v___x_3484_ = l_Lean_Expr_hasMVar(v_e_3056_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_inc_ref(v_e_3056_);
v___x_3485_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3551_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3551_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3551_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3530_; lean_object* v_cache_3531_; lean_object* v_inferType_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_st_ref_get(v_a_3058_);
v_cache_3531_ = lean_ctor_get(v___x_3530_, 1);
lean_inc_ref(v_cache_3531_);
lean_dec(v___x_3530_);
v_inferType_3532_ = lean_ctor_get(v_cache_3531_, 0);
lean_inc_ref(v_inferType_3532_);
lean_dec_ref(v_cache_3531_);
v___x_3533_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3532_, v_a_3486_);
lean_dec_ref(v_inferType_3532_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_toCold_3534_; lean_object* v_cancelTk_x3f_3535_; 
lean_del_object(v___x_3488_);
v_toCold_3534_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3535_ = lean_ctor_get(v_toCold_3534_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3535_) == 1)
{
lean_object* v_val_3536_; uint8_t v___x_3537_; 
v_val_3536_ = lean_ctor_get(v_cancelTk_x3f_3535_, 0);
v___x_3537_ = l_IO_CancelToken_isSet(v_val_3536_);
if (v___x_3537_ == 0)
{
goto v___jp_3490_;
}
else
{
lean_object* v___x_3538_; lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3486_);
lean_dec_ref(v_e_3056_);
v___x_3538_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
goto v___jp_3490_;
}
}
else
{
lean_object* v_val_3547_; lean_object* v___x_3549_; 
lean_dec(v_a_3486_);
lean_dec_ref(v_e_3056_);
v_val_3547_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3533_, 1);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_val_3547_);
v___x_3549_ = v___x_3488_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_val_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
v___jp_3490_:
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; uint8_t v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
v___x_3493_ = l_Lean_Expr_hasMVar(v_a_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3528_; 
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v___x_3491_, 0);
lean_dec(v_unused_3529_);
v___x_3495_ = v___x_3491_;
v_isShared_3496_ = v_isSharedCheck_3528_;
goto v_resetjp_3494_;
}
else
{
lean_dec(v___x_3491_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3528_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v_cache_3498_; lean_object* v_mctx_3499_; lean_object* v_zetaDeltaFVarIds_3500_; lean_object* v_postponed_3501_; lean_object* v_diag_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3527_; 
v___x_3497_ = lean_st_ref_take(v_a_3058_);
v_cache_3498_ = lean_ctor_get(v___x_3497_, 1);
v_mctx_3499_ = lean_ctor_get(v___x_3497_, 0);
v_zetaDeltaFVarIds_3500_ = lean_ctor_get(v___x_3497_, 2);
v_postponed_3501_ = lean_ctor_get(v___x_3497_, 3);
v_diag_3502_ = lean_ctor_get(v___x_3497_, 4);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3504_ = v___x_3497_;
v_isShared_3505_ = v_isSharedCheck_3527_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_diag_3502_);
lean_inc(v_postponed_3501_);
lean_inc(v_zetaDeltaFVarIds_3500_);
lean_inc(v_cache_3498_);
lean_inc(v_mctx_3499_);
lean_dec(v___x_3497_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3527_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_inferType_3506_; lean_object* v_funInfo_3507_; lean_object* v_synthInstance_3508_; lean_object* v_whnf_3509_; lean_object* v_defEqTrans_3510_; lean_object* v_defEqPerm_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3526_; 
v_inferType_3506_ = lean_ctor_get(v_cache_3498_, 0);
v_funInfo_3507_ = lean_ctor_get(v_cache_3498_, 1);
v_synthInstance_3508_ = lean_ctor_get(v_cache_3498_, 2);
v_whnf_3509_ = lean_ctor_get(v_cache_3498_, 3);
v_defEqTrans_3510_ = lean_ctor_get(v_cache_3498_, 4);
v_defEqPerm_3511_ = lean_ctor_get(v_cache_3498_, 5);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_cache_3498_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3513_ = v_cache_3498_;
v_isShared_3514_ = v_isSharedCheck_3526_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_defEqPerm_3511_);
lean_inc(v_defEqTrans_3510_);
lean_inc(v_whnf_3509_);
lean_inc(v_synthInstance_3508_);
lean_inc(v_funInfo_3507_);
lean_inc(v_inferType_3506_);
lean_dec(v_cache_3498_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3526_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
lean_inc(v_a_3492_);
v___x_3515_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3506_, v_a_3486_, v_a_3492_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3515_);
v___x_3517_ = v___x_3513_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_funInfo_3507_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_synthInstance_3508_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_whnf_3509_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_defEqTrans_3510_);
lean_ctor_set(v_reuseFailAlloc_3525_, 5, v_defEqPerm_3511_);
v___x_3517_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v___x_3517_);
v___x_3519_ = v___x_3504_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_mctx_3499_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_zetaDeltaFVarIds_3500_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_postponed_3501_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_diag_3502_);
v___x_3519_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = lean_st_ref_put(v_a_3058_, v___x_3519_);
if (v_isShared_3496_ == 0)
{
v___x_3522_ = v___x_3495_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3492_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3492_);
lean_dec(v_a_3486_);
return v___x_3491_;
}
}
else
{
lean_dec(v_a_3486_);
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec_ref(v_e_3056_);
v_a_3552_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3485_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3485_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
goto v___jp_3062_;
}
}
}
}
v___jp_3062_:
{
lean_object* v_toCold_3063_; lean_object* v_cancelTk_x3f_3064_; 
v_toCold_3063_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3064_ = lean_ctor_get(v_toCold_3063_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3064_) == 1)
{
lean_object* v_val_3065_; uint8_t v___x_3066_; 
v_val_3065_ = lean_ctor_get(v_cancelTk_x3f_3064_, 0);
v___x_3066_ = l_IO_CancelToken_isSet(v_val_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3067_;
}
else
{
lean_object* v___x_3068_; lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v_e_3056_);
v___x_3068_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3077_;
}
}
v___jp_3078_:
{
lean_object* v_toCold_3079_; lean_object* v_cancelTk_x3f_3080_; 
v_toCold_3079_ = lean_ctor_get(v_a_3059_, 0);
v_cancelTk_x3f_3080_ = lean_ctor_get(v_toCold_3079_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3080_) == 1)
{
lean_object* v_val_3081_; uint8_t v___x_3082_; 
v_val_3081_ = lean_ctor_get(v_cancelTk_x3f_3080_, 0);
v___x_3082_ = l_IO_CancelToken_isSet(v_val_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v_e_3056_);
v___x_3084_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
return v___x_3093_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3568_, v_x_3569_, v_x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3576_, lean_object* v_x_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3576_, v_x_3577_, v_x_3578_);
lean_dec_ref(v_x_3578_);
lean_dec_ref(v_x_3577_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, size_t v_x_3582_, size_t v_x_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3581_, v_x_3582_, v_x_3583_, v_x_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
size_t v_x_4028__boxed_3593_; size_t v_x_4029__boxed_3594_; lean_object* v_res_3595_; 
v_x_4028__boxed_3593_ = lean_unbox_usize(v_x_3589_);
lean_dec(v_x_3589_);
v_x_4029__boxed_3594_ = lean_unbox_usize(v_x_3590_);
lean_dec(v_x_3590_);
v_res_3595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3587_, v_x_3588_, v_x_4028__boxed_3593_, v_x_4029__boxed_3594_, v_x_3591_, v_x_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3596_, lean_object* v_x_3597_, size_t v_x_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3597_, v_x_3598_, v_x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
size_t v_x_4045__boxed_3605_; lean_object* v_res_3606_; 
v_x_4045__boxed_3605_ = lean_unbox_usize(v_x_3603_);
lean_dec(v_x_3603_);
v_res_3606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3601_, v_x_3602_, v_x_4045__boxed_3605_, v_x_3604_);
lean_dec_ref(v_x_3604_);
lean_dec_ref(v_x_3602_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3607_, lean_object* v_n_3608_, lean_object* v_k_3609_, lean_object* v_v_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3608_, v_k_3609_, v_v_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3612_, size_t v_depth_3613_, lean_object* v_keys_3614_, lean_object* v_vals_3615_, lean_object* v_heq_3616_, lean_object* v_i_3617_, lean_object* v_entries_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3613_, v_keys_3614_, v_vals_3615_, v_i_3617_, v_entries_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3620_, lean_object* v_depth_3621_, lean_object* v_keys_3622_, lean_object* v_vals_3623_, lean_object* v_heq_3624_, lean_object* v_i_3625_, lean_object* v_entries_3626_){
_start:
{
size_t v_depth_boxed_3627_; lean_object* v_res_3628_; 
v_depth_boxed_3627_ = lean_unbox_usize(v_depth_3621_);
lean_dec(v_depth_3621_);
v_res_3628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3620_, v_depth_boxed_3627_, v_keys_3622_, v_vals_3623_, v_heq_3624_, v_i_3625_, v_entries_3626_);
lean_dec_ref(v_vals_3623_);
lean_dec_ref(v_keys_3622_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3629_, lean_object* v_keys_3630_, lean_object* v_vals_3631_, lean_object* v_heq_3632_, lean_object* v_i_3633_, lean_object* v_k_3634_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3630_, v_vals_3631_, v_i_3633_, v_k_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3636_, lean_object* v_keys_3637_, lean_object* v_vals_3638_, lean_object* v_heq_3639_, lean_object* v_i_3640_, lean_object* v_k_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3636_, v_keys_3637_, v_vals_3638_, v_heq_3639_, v_i_3640_, v_k_3641_);
lean_dec_ref(v_k_3641_);
lean_dec_ref(v_vals_3638_);
lean_dec_ref(v_keys_3637_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3644_, v_x_3645_, v_x_3646_, v_x_3647_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = l_Lean_maxRecDepthErrorMessage;
v___x_3655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3657_ = l_Lean_MessageData_ofFormat(v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3659_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3660_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___x_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3661_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_ref_3661_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3669_, lean_object* v_ref_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3670_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_ref_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3677_, v_ref_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3737_; uint8_t v_beta_3738_; 
v___x_3737_ = l_Lean_Meta_Context_config(v___y_3686_);
v_beta_3738_ = lean_ctor_get_uint8(v___x_3737_, 13);
if (v_beta_3738_ == 0)
{
lean_dec_ref(v___x_3737_);
goto v___jp_3691_;
}
else
{
uint8_t v_iota_3739_; 
v_iota_3739_ = lean_ctor_get_uint8(v___x_3737_, 12);
if (v_iota_3739_ == 0)
{
lean_dec_ref(v___x_3737_);
goto v___jp_3691_;
}
else
{
uint8_t v_zeta_3740_; 
v_zeta_3740_ = lean_ctor_get_uint8(v___x_3737_, 15);
if (v_zeta_3740_ == 0)
{
lean_dec_ref(v___x_3737_);
goto v___jp_3691_;
}
else
{
uint8_t v_zetaHave_3741_; 
v_zetaHave_3741_ = lean_ctor_get_uint8(v___x_3737_, 18);
if (v_zetaHave_3741_ == 0)
{
lean_dec_ref(v___x_3737_);
goto v___jp_3691_;
}
else
{
uint8_t v_zetaDelta_3742_; 
v_zetaDelta_3742_ = lean_ctor_get_uint8(v___x_3737_, 16);
if (v_zetaDelta_3742_ == 0)
{
lean_dec_ref(v___x_3737_);
goto v___jp_3691_;
}
else
{
uint8_t v_etaStruct_3743_; uint8_t v_proj_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_etaStruct_3743_ = lean_ctor_get_uint8(v___x_3737_, 10);
v_proj_3744_ = lean_ctor_get_uint8(v___x_3737_, 14);
lean_dec_ref(v___x_3737_);
v___x_3745_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_3744_);
v___x_3746_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_3747_ = lean_nat_dec_eq(v___x_3745_, v___x_3746_);
lean_dec(v___x_3745_);
if (v___x_3747_ == 0)
{
goto v___jp_3691_;
}
else
{
uint8_t v___x_3748_; uint8_t v___x_3749_; 
v___x_3748_ = 0;
v___x_3749_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3743_, v___x_3748_);
if (v___x_3749_ == 0)
{
goto v___jp_3691_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec_ref(v___y_3686_);
return v___x_3750_;
}
}
}
}
}
}
}
v___jp_3691_:
{
lean_object* v___x_3692_; uint8_t v_foApprox_3693_; uint8_t v_ctxApprox_3694_; uint8_t v_quasiPatternApprox_3695_; uint8_t v_constApprox_3696_; uint8_t v_isDefEqStuckEx_3697_; uint8_t v_unificationHints_3698_; uint8_t v_proofIrrelevance_3699_; uint8_t v_assignSyntheticOpaque_3700_; uint8_t v_offsetCnstrs_3701_; uint8_t v_transparency_3702_; uint8_t v_univApprox_3703_; uint8_t v_zetaUnused_3704_; uint8_t v_canUnfoldPredicateConfig_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3736_; 
v___x_3692_ = l_Lean_Meta_Context_config(v___y_3686_);
v_foApprox_3693_ = lean_ctor_get_uint8(v___x_3692_, 0);
v_ctxApprox_3694_ = lean_ctor_get_uint8(v___x_3692_, 1);
v_quasiPatternApprox_3695_ = lean_ctor_get_uint8(v___x_3692_, 2);
v_constApprox_3696_ = lean_ctor_get_uint8(v___x_3692_, 3);
v_isDefEqStuckEx_3697_ = lean_ctor_get_uint8(v___x_3692_, 4);
v_unificationHints_3698_ = lean_ctor_get_uint8(v___x_3692_, 5);
v_proofIrrelevance_3699_ = lean_ctor_get_uint8(v___x_3692_, 6);
v_assignSyntheticOpaque_3700_ = lean_ctor_get_uint8(v___x_3692_, 7);
v_offsetCnstrs_3701_ = lean_ctor_get_uint8(v___x_3692_, 8);
v_transparency_3702_ = lean_ctor_get_uint8(v___x_3692_, 9);
v_univApprox_3703_ = lean_ctor_get_uint8(v___x_3692_, 11);
v_zetaUnused_3704_ = lean_ctor_get_uint8(v___x_3692_, 17);
v_canUnfoldPredicateConfig_3705_ = lean_ctor_get_uint8(v___x_3692_, 19);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3707_ = v___x_3692_;
v_isShared_3708_ = v_isSharedCheck_3736_;
goto v_resetjp_3706_;
}
else
{
lean_dec(v___x_3692_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3736_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
uint8_t v___x_3709_; uint8_t v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3713_; 
v___x_3709_ = 1;
v___x_3710_ = 0;
v___x_3711_ = 2;
if (v_isShared_3708_ == 0)
{
v___x_3713_ = v___x_3707_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 0, v_foApprox_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 1, v_ctxApprox_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 2, v_quasiPatternApprox_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 3, v_constApprox_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 4, v_isDefEqStuckEx_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 5, v_unificationHints_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 6, v_proofIrrelevance_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 7, v_assignSyntheticOpaque_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 8, v_offsetCnstrs_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 9, v_transparency_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 11, v_univApprox_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 17, v_zetaUnused_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3735_, 19, v_canUnfoldPredicateConfig_3705_);
v___x_3713_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
uint8_t v_trackZetaDelta_3714_; lean_object* v_zetaDeltaSet_3715_; lean_object* v_lctx_3716_; lean_object* v_localInstances_3717_; lean_object* v_defEqCtx_x3f_3718_; lean_object* v_synthPendingDepth_3719_; lean_object* v_customCanUnfoldPredicate_x3f_3720_; uint8_t v_univApprox_3721_; uint8_t v_inTypeClassResolution_3722_; uint8_t v_cacheInferType_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3733_; 
lean_ctor_set_uint8(v___x_3713_, 10, v___x_3710_);
lean_ctor_set_uint8(v___x_3713_, 12, v___x_3709_);
lean_ctor_set_uint8(v___x_3713_, 13, v___x_3709_);
lean_ctor_set_uint8(v___x_3713_, 14, v___x_3711_);
lean_ctor_set_uint8(v___x_3713_, 15, v___x_3709_);
lean_ctor_set_uint8(v___x_3713_, 16, v___x_3709_);
lean_ctor_set_uint8(v___x_3713_, 18, v___x_3709_);
v_trackZetaDelta_3714_ = lean_ctor_get_uint8(v___y_3686_, sizeof(void*)*7);
v_zetaDeltaSet_3715_ = lean_ctor_get(v___y_3686_, 1);
v_lctx_3716_ = lean_ctor_get(v___y_3686_, 2);
v_localInstances_3717_ = lean_ctor_get(v___y_3686_, 3);
v_defEqCtx_x3f_3718_ = lean_ctor_get(v___y_3686_, 4);
v_synthPendingDepth_3719_ = lean_ctor_get(v___y_3686_, 5);
v_customCanUnfoldPredicate_x3f_3720_ = lean_ctor_get(v___y_3686_, 6);
v_univApprox_3721_ = lean_ctor_get_uint8(v___y_3686_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3722_ = lean_ctor_get_uint8(v___y_3686_, sizeof(void*)*7 + 2);
v_cacheInferType_3723_ = lean_ctor_get_uint8(v___y_3686_, sizeof(void*)*7 + 3);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___y_3686_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___y_3686_, 0);
lean_dec(v_unused_3734_);
v___x_3725_ = v___y_3686_;
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3720_);
lean_inc(v_synthPendingDepth_3719_);
lean_inc(v_defEqCtx_x3f_3718_);
lean_inc(v_localInstances_3717_);
lean_inc(v_lctx_3716_);
lean_inc(v_zetaDeltaSet_3715_);
lean_dec(v___y_3686_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
uint64_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3713_);
v___x_3728_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3728_, 0, v___x_3713_);
lean_ctor_set_uint64(v___x_3728_, sizeof(void*)*1, v___x_3727_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3728_);
v___x_3730_ = v___x_3725_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_zetaDeltaSet_3715_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_lctx_3716_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_localInstances_3717_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_defEqCtx_x3f_3718_);
lean_ctor_set(v_reuseFailAlloc_3732_, 5, v_synthPendingDepth_3719_);
lean_ctor_set(v_reuseFailAlloc_3732_, 6, v_customCanUnfoldPredicate_x3f_3720_);
lean_ctor_set_uint8(v_reuseFailAlloc_3732_, sizeof(void*)*7, v_trackZetaDelta_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3732_, sizeof(void*)*7 + 1, v_univApprox_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3732_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3732_, sizeof(void*)*7 + 3, v_cacheInferType_3723_);
v___x_3730_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3731_; 
v___x_3731_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3685_, v___x_3730_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec_ref(v___x_3730_);
return v___x_3731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v___y_3765_; lean_object* v_toCold_3782_; lean_object* v_currRecDepth_3783_; lean_object* v_ref_3784_; uint8_t v_diag_3785_; uint8_t v_suppressElabErrors_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3826_; 
v_toCold_3782_ = lean_ctor_get(v_a_3761_, 0);
v_currRecDepth_3783_ = lean_ctor_get(v_a_3761_, 1);
v_ref_3784_ = lean_ctor_get(v_a_3761_, 2);
v_diag_3785_ = lean_ctor_get_uint8(v_a_3761_, sizeof(void*)*3);
v_suppressElabErrors_3786_ = lean_ctor_get_uint8(v_a_3761_, sizeof(void*)*3 + 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_a_3761_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3788_ = v_a_3761_;
v_isShared_3789_ = v_isSharedCheck_3826_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_ref_3784_);
lean_inc(v_currRecDepth_3783_);
lean_inc(v_toCold_3782_);
lean_dec(v_a_3761_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3826_;
goto v_resetjp_3787_;
}
v___jp_3764_:
{
if (lean_obj_tag(v___y_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
v_a_3766_ = lean_ctor_get(v___y_3765_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___y_3765_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___y_3765_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___y_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
v_a_3774_ = lean_ctor_get(v___y_3765_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___y_3765_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___y_3765_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___y_3765_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
v_resetjp_3787_:
{
lean_object* v_maxRecDepth_3790_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_maxRecDepth_3790_ = lean_ctor_get(v_toCold_3782_, 3);
v___x_3822_ = lean_unsigned_to_nat(0u);
v___x_3823_ = lean_nat_dec_eq(v_maxRecDepth_3790_, v___x_3822_);
if (v___x_3823_ == 0)
{
uint8_t v___x_3824_; 
v___x_3824_ = lean_nat_dec_eq(v_currRecDepth_3783_, v_maxRecDepth_3790_);
if (v___x_3824_ == 0)
{
goto v___jp_3791_;
}
else
{
lean_object* v___x_3825_; 
lean_del_object(v___x_3788_);
lean_dec(v_currRecDepth_3783_);
lean_dec_ref(v_toCold_3782_);
lean_dec(v_a_3762_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec_ref(v_e_3758_);
v___x_3825_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3784_);
return v___x_3825_;
}
}
else
{
goto v___jp_3791_;
}
v___jp_3791_:
{
lean_object* v___x_3792_; uint8_t v_transparency_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3792_ = l_Lean_Meta_Context_config(v_a_3759_);
v_transparency_3793_ = lean_ctor_get_uint8(v___x_3792_, 9);
lean_dec_ref(v___x_3792_);
v___x_3794_ = lean_unsigned_to_nat(1u);
v___x_3795_ = lean_nat_add(v_currRecDepth_3783_, v___x_3794_);
lean_dec(v_currRecDepth_3783_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___x_3795_);
v___x_3797_ = v___x_3788_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_toCold_3782_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3821_, 2, v_ref_3784_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*3, v_diag_3785_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*3 + 1, v_suppressElabErrors_3786_);
v___x_3797_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
uint8_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = 1;
v___x_3799_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3793_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; 
v___x_3800_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3758_, v_a_3759_, v_a_3760_, v___x_3797_, v_a_3762_);
lean_dec(v_a_3762_);
lean_dec_ref(v___x_3797_);
lean_dec(v_a_3760_);
v___y_3765_ = v___x_3800_;
goto v___jp_3764_;
}
else
{
lean_object* v_keyedConfig_3801_; uint8_t v_trackZetaDelta_3802_; lean_object* v_zetaDeltaSet_3803_; lean_object* v_lctx_3804_; lean_object* v_localInstances_3805_; lean_object* v_defEqCtx_x3f_3806_; lean_object* v_synthPendingDepth_3807_; lean_object* v_customCanUnfoldPredicate_x3f_3808_; uint8_t v_univApprox_3809_; uint8_t v_inTypeClassResolution_3810_; uint8_t v_cacheInferType_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3820_; 
v_keyedConfig_3801_ = lean_ctor_get(v_a_3759_, 0);
v_trackZetaDelta_3802_ = lean_ctor_get_uint8(v_a_3759_, sizeof(void*)*7);
v_zetaDeltaSet_3803_ = lean_ctor_get(v_a_3759_, 1);
v_lctx_3804_ = lean_ctor_get(v_a_3759_, 2);
v_localInstances_3805_ = lean_ctor_get(v_a_3759_, 3);
v_defEqCtx_x3f_3806_ = lean_ctor_get(v_a_3759_, 4);
v_synthPendingDepth_3807_ = lean_ctor_get(v_a_3759_, 5);
v_customCanUnfoldPredicate_x3f_3808_ = lean_ctor_get(v_a_3759_, 6);
v_univApprox_3809_ = lean_ctor_get_uint8(v_a_3759_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3810_ = lean_ctor_get_uint8(v_a_3759_, sizeof(void*)*7 + 2);
v_cacheInferType_3811_ = lean_ctor_get_uint8(v_a_3759_, sizeof(void*)*7 + 3);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_a_3759_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3813_ = v_a_3759_;
v_isShared_3814_ = v_isSharedCheck_3820_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3808_);
lean_inc(v_synthPendingDepth_3807_);
lean_inc(v_defEqCtx_x3f_3806_);
lean_inc(v_localInstances_3805_);
lean_inc(v_lctx_3804_);
lean_inc(v_zetaDeltaSet_3803_);
lean_inc(v_keyedConfig_3801_);
lean_dec(v_a_3759_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3820_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3815_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3798_, v_keyedConfig_3801_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v___x_3815_);
v___x_3817_ = v___x_3813_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_zetaDeltaSet_3803_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_lctx_3804_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_localInstances_3805_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_defEqCtx_x3f_3806_);
lean_ctor_set(v_reuseFailAlloc_3819_, 5, v_synthPendingDepth_3807_);
lean_ctor_set(v_reuseFailAlloc_3819_, 6, v_customCanUnfoldPredicate_x3f_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3819_, sizeof(void*)*7, v_trackZetaDelta_3802_);
lean_ctor_set_uint8(v_reuseFailAlloc_3819_, sizeof(void*)*7 + 1, v_univApprox_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3819_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3819_, sizeof(void*)*7 + 3, v_cacheInferType_3811_);
v___x_3817_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3758_, v___x_3817_, v_a_3760_, v___x_3797_, v_a_3762_);
lean_dec(v_a_3762_);
lean_dec_ref(v___x_3797_);
lean_dec(v_a_3760_);
v___y_3765_ = v___x_3818_;
goto v___jp_3764_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = lean_infer_type(v_e_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
return v_res_3833_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3834_){
_start:
{
switch(lean_obj_tag(v_x_3834_))
{
case 0:
{
uint8_t v___x_3835_; 
v___x_3835_ = 1;
return v___x_3835_;
}
case 2:
{
lean_object* v_a_3836_; lean_object* v_a_3837_; uint8_t v___x_3838_; 
v_a_3836_ = lean_ctor_get(v_x_3834_, 0);
v_a_3837_ = lean_ctor_get(v_x_3834_, 1);
v___x_3838_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3836_);
if (v___x_3838_ == 0)
{
return v___x_3838_;
}
else
{
v_x_3834_ = v_a_3837_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3840_; 
v_a_3840_ = lean_ctor_get(v_x_3834_, 1);
v_x_3834_ = v_a_3840_;
goto _start;
}
default: 
{
uint8_t v___x_3842_; 
v___x_3842_ = 0;
return v___x_3842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3843_){
_start:
{
uint8_t v_res_3844_; lean_object* v_r_3845_; 
v_res_3844_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3843_);
lean_dec(v_x_3843_);
v_r_3845_ = lean_box(v_res_3844_);
return v_r_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; lean_object* v_mctx_3850_; lean_object* v___x_3851_; lean_object* v_fst_3852_; lean_object* v_snd_3853_; lean_object* v___x_3854_; lean_object* v_cache_3855_; lean_object* v_zetaDeltaFVarIds_3856_; lean_object* v_postponed_3857_; lean_object* v_diag_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3867_; 
v___x_3849_ = lean_st_ref_get(v___y_3847_);
v_mctx_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc_ref(v_mctx_3850_);
lean_dec(v___x_3849_);
v___x_3851_ = lean_instantiate_level_mvars(v_mctx_3850_, v_l_3846_);
v_fst_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_fst_3852_);
v_snd_3853_ = lean_ctor_get(v___x_3851_, 1);
lean_inc(v_snd_3853_);
lean_dec_ref(v___x_3851_);
v___x_3854_ = lean_st_ref_take(v___y_3847_);
v_cache_3855_ = lean_ctor_get(v___x_3854_, 1);
v_zetaDeltaFVarIds_3856_ = lean_ctor_get(v___x_3854_, 2);
v_postponed_3857_ = lean_ctor_get(v___x_3854_, 3);
v_diag_3858_ = lean_ctor_get(v___x_3854_, 4);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v___x_3854_, 0);
lean_dec(v_unused_3868_);
v___x_3860_ = v___x_3854_;
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_diag_3858_);
lean_inc(v_postponed_3857_);
lean_inc(v_zetaDeltaFVarIds_3856_);
lean_inc(v_cache_3855_);
lean_dec(v___x_3854_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v_fst_3852_);
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_fst_3852_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_cache_3855_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_zetaDeltaFVarIds_3856_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_postponed_3857_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_diag_3858_);
v___x_3863_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_st_ref_put(v___y_3847_, v___x_3863_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_snd_3853_);
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3869_, v___y_3870_);
lean_dec(v___y_3870_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3873_, v___y_3875_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
switch(lean_obj_tag(v_x_3887_))
{
case 3:
{
lean_object* v_u_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_u_3898_ = lean_ctor_get(v_x_3887_, 0);
lean_inc(v_u_3898_);
lean_dec_ref_known(v_x_3887_, 1);
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_nat_dec_eq(v_x_3888_, v___x_3899_);
lean_dec(v_x_3888_);
if (v___x_3900_ == 0)
{
lean_dec(v_u_3898_);
goto v___jp_3894_;
}
else
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3898_, v_a_3890_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3912_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3912_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
uint8_t v___x_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3906_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3902_);
lean_dec(v_a_3902_);
v___x_3907_ = l_Lean_Bool_toLBool(v___x_3906_);
v___x_3908_ = lean_box(v___x_3907_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3908_);
v___x_3910_ = v___x_3904_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3901_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3901_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3921_; lean_object* v_zero_3922_; uint8_t v_isZero_3923_; 
v_body_3921_ = lean_ctor_get(v_x_3887_, 2);
lean_inc_ref(v_body_3921_);
lean_dec_ref_known(v_x_3887_, 3);
v_zero_3922_ = lean_unsigned_to_nat(0u);
v_isZero_3923_ = lean_nat_dec_eq(v_x_3888_, v_zero_3922_);
if (v_isZero_3923_ == 1)
{
uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_dec_ref(v_body_3921_);
lean_dec(v_x_3888_);
v___x_3924_ = 0;
v___x_3925_ = lean_box(v___x_3924_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
return v___x_3926_;
}
else
{
lean_object* v_one_3927_; lean_object* v_n_3928_; 
v_one_3927_ = lean_unsigned_to_nat(1u);
v_n_3928_ = lean_nat_sub(v_x_3888_, v_one_3927_);
lean_dec(v_x_3888_);
v_x_3887_ = v_body_3921_;
v_x_3888_ = v_n_3928_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3930_; 
v_body_3930_ = lean_ctor_get(v_x_3887_, 3);
lean_inc_ref(v_body_3930_);
lean_dec_ref_known(v_x_3887_, 4);
v_x_3887_ = v_body_3930_;
goto _start;
}
case 10:
{
lean_object* v_expr_3932_; 
v_expr_3932_ = lean_ctor_get(v_x_3887_, 1);
lean_inc_ref(v_expr_3932_);
lean_dec_ref_known(v_x_3887_, 2);
v_x_3887_ = v_expr_3932_;
goto _start;
}
default: 
{
lean_dec(v_x_3888_);
lean_dec_ref(v_x_3887_);
goto v___jp_3894_;
}
}
v___jp_3894_:
{
uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = 2;
v___x_3896_ = lean_box(v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3934_, lean_object* v_x_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3934_, v_x_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3942_, lean_object* v_x_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
switch(lean_obj_tag(v_x_3942_))
{
case 4:
{
lean_object* v_declName_3949_; lean_object* v_us_3950_; lean_object* v___x_3951_; 
v_declName_3949_ = lean_ctor_get(v_x_3942_, 0);
lean_inc(v_declName_3949_);
v_us_3950_ = lean_ctor_get(v_x_3942_, 1);
lean_inc(v_us_3950_);
lean_dec_ref_known(v_x_3942_, 2);
v___x_3951_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3949_, v_us_3950_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3952_, v_x_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3953_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_x_3943_);
v_a_3954_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3951_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3951_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3962_; lean_object* v___x_3963_; 
v_fvarId_3962_ = lean_ctor_get(v_x_3942_, 0);
lean_inc(v_fvarId_3962_);
lean_dec_ref_known(v_x_3942_, 1);
v___x_3963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3962_, v_a_3944_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3964_, v_x_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3965_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_x_3943_);
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
case 2:
{
lean_object* v_mvarId_3974_; lean_object* v___x_3975_; 
v_mvarId_3974_ = lean_ctor_get(v_x_3942_, 0);
lean_inc(v_mvarId_3974_);
lean_dec_ref_known(v_x_3942_, 1);
v___x_3975_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3974_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3977_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3976_, v_x_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3977_;
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_x_3943_);
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
case 5:
{
lean_object* v_fn_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_fn_3986_ = lean_ctor_get(v_x_3942_, 0);
lean_inc_ref(v_fn_3986_);
lean_dec_ref_known(v_x_3942_, 2);
v___x_3987_ = lean_unsigned_to_nat(1u);
v___x_3988_ = lean_nat_add(v_x_3943_, v___x_3987_);
lean_dec(v_x_3943_);
v_x_3942_ = v_fn_3986_;
v_x_3943_ = v___x_3988_;
goto _start;
}
case 10:
{
lean_object* v_expr_3990_; 
v_expr_3990_ = lean_ctor_get(v_x_3942_, 1);
lean_inc_ref(v_expr_3990_);
lean_dec_ref_known(v_x_3942_, 2);
v_x_3942_ = v_expr_3990_;
goto _start;
}
case 8:
{
lean_object* v_body_3992_; 
v_body_3992_ = lean_ctor_get(v_x_3942_, 3);
lean_inc_ref(v_body_3992_);
lean_dec_ref_known(v_x_3942_, 4);
v_x_3942_ = v_body_3992_;
goto _start;
}
case 6:
{
lean_object* v_body_3994_; lean_object* v_zero_3995_; uint8_t v_isZero_3996_; 
v_body_3994_ = lean_ctor_get(v_x_3942_, 2);
lean_inc_ref(v_body_3994_);
lean_dec_ref_known(v_x_3942_, 3);
v_zero_3995_ = lean_unsigned_to_nat(0u);
v_isZero_3996_ = lean_nat_dec_eq(v_x_3943_, v_zero_3995_);
if (v_isZero_3996_ == 1)
{
uint8_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_body_3994_);
lean_dec(v_x_3943_);
v___x_3997_ = 0;
v___x_3998_ = lean_box(v___x_3997_);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
else
{
lean_object* v_one_4000_; lean_object* v_n_4001_; 
v_one_4000_ = lean_unsigned_to_nat(1u);
v_n_4001_ = lean_nat_sub(v_x_3943_, v_one_4000_);
lean_dec(v_x_3943_);
v_x_3942_ = v_body_3994_;
v_x_3943_ = v_n_4001_;
goto _start;
}
}
default: 
{
uint8_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec(v_x_3943_);
lean_dec_ref(v_x_3942_);
v___x_4003_ = 2;
v___x_4004_ = lean_box(v___x_4003_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4006_, lean_object* v_x_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4006_, v_x_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
switch(lean_obj_tag(v_x_4014_))
{
case 0:
{
uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_dec_ref_known(v_x_4014_, 1);
v___x_4020_ = 2;
v___x_4021_ = lean_box(v___x_4020_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
case 1:
{
lean_object* v_fvarId_4023_; lean_object* v___x_4024_; 
v_fvarId_4023_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_fvarId_4023_);
lean_dec_ref_known(v_x_4014_, 1);
v___x_4024_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4023_, v_a_4015_, v_a_4017_, v_a_4018_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4025_, v___x_4026_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
return v___x_4027_;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4024_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4024_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4036_; lean_object* v___x_4037_; 
v_mvarId_4036_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_mvarId_4036_);
lean_dec_ref_known(v_x_4014_, 1);
v___x_4037_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4036_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4038_, v___x_4039_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
return v___x_4040_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
v_a_4041_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4037_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4037_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
case 4:
{
lean_object* v_declName_4049_; lean_object* v_us_4050_; lean_object* v___x_4051_; 
v_declName_4049_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_declName_4049_);
v_us_4050_ = lean_ctor_get(v_x_4014_, 1);
lean_inc(v_us_4050_);
lean_dec_ref_known(v_x_4014_, 2);
v___x_4051_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4049_, v_us_4050_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4051_, 1);
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4052_, v___x_4053_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
return v___x_4054_;
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_a_4055_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4051_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4051_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
case 5:
{
lean_object* v_fn_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_fn_4063_ = lean_ctor_get(v_x_4014_, 0);
lean_inc_ref(v_fn_4063_);
lean_dec_ref_known(v_x_4014_, 2);
v___x_4064_ = lean_unsigned_to_nat(1u);
v___x_4065_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4063_, v___x_4064_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
return v___x_4065_;
}
case 7:
{
lean_object* v_body_4066_; 
v_body_4066_ = lean_ctor_get(v_x_4014_, 2);
lean_inc_ref(v_body_4066_);
lean_dec_ref_known(v_x_4014_, 3);
v_x_4014_ = v_body_4066_;
goto _start;
}
case 8:
{
lean_object* v_body_4068_; 
v_body_4068_ = lean_ctor_get(v_x_4014_, 3);
lean_inc_ref(v_body_4068_);
lean_dec_ref_known(v_x_4014_, 4);
v_x_4014_ = v_body_4068_;
goto _start;
}
case 10:
{
lean_object* v_expr_4070_; 
v_expr_4070_ = lean_ctor_get(v_x_4014_, 1);
lean_inc_ref(v_expr_4070_);
lean_dec_ref_known(v_x_4014_, 2);
v_x_4014_ = v_expr_4070_;
goto _start;
}
case 11:
{
uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_dec_ref_known(v_x_4014_, 3);
v___x_4072_ = 2;
v___x_4073_ = lean_box(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
default: 
{
uint8_t v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref(v_x_4014_);
v___x_4075_ = 0;
v___x_4076_ = lean_box(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Meta_isPropQuick(v_x_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v___x_4091_; 
lean_inc_ref(v_e_4085_);
v___x_4091_ = l_Lean_Meta_isPropQuick(v_e_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4148_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4148_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4148_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
uint8_t v___x_4096_; 
v___x_4096_ = lean_unbox(v_a_4092_);
lean_dec(v_a_4092_);
switch(v___x_4096_)
{
case 0:
{
uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
lean_dec_ref(v_e_4085_);
v___x_4097_ = 0;
v___x_4098_ = lean_box(v___x_4097_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4098_);
v___x_4100_ = v___x_4094_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
case 1:
{
uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_dec_ref(v_e_4085_);
v___x_4102_ = 1;
v___x_4103_ = lean_box(v___x_4102_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4103_);
v___x_4105_ = v___x_4094_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
default: 
{
lean_object* v___x_4107_; 
lean_del_object(v___x_4094_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
lean_inc(v_a_4087_);
lean_inc_ref(v_a_4086_);
v___x_4107_ = lean_infer_type(v_e_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4109_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4107_, 1);
v___x_4109_ = l_Lean_Meta_whnfD(v_a_4108_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4131_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4131_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4131_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
if (lean_obj_tag(v_a_4110_) == 3)
{
lean_object* v_u_4114_; lean_object* v___x_4115_; lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4125_; 
lean_del_object(v___x_4112_);
v_u_4114_ = lean_ctor_get(v_a_4110_, 0);
lean_inc(v_u_4114_);
lean_dec_ref_known(v_a_4110_, 1);
v___x_4115_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4114_, v_a_4087_);
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4125_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4125_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4120_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4116_);
lean_dec(v_a_4116_);
v___x_4121_ = lean_box(v___x_4120_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4121_);
v___x_4123_ = v___x_4118_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
else
{
uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4129_; 
lean_dec(v_a_4110_);
v___x_4126_ = 0;
v___x_4127_ = lean_box(v___x_4126_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 0, v___x_4127_);
v___x_4129_ = v___x_4112_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_a_4132_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4109_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4109_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_a_4140_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4107_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4107_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref(v_e_4085_);
v_a_4149_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4091_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4091_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_Meta_isProp(v_e_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4164_){
_start:
{
switch(lean_obj_tag(v_x_4164_))
{
case 0:
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_unsigned_to_nat(0u);
return v___x_4165_;
}
case 1:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_unsigned_to_nat(1u);
return v___x_4166_;
}
case 2:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_unsigned_to_nat(2u);
return v___x_4167_;
}
default: 
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_unsigned_to_nat(3u);
return v___x_4168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4169_);
lean_dec(v_x_4169_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4171_, lean_object* v_k_4172_){
_start:
{
if (lean_obj_tag(v_t_4171_) == 3)
{
lean_object* v_idx_4173_; lean_object* v___x_4174_; 
v_idx_4173_ = lean_ctor_get(v_t_4171_, 0);
lean_inc(v_idx_4173_);
lean_dec_ref_known(v_t_4171_, 1);
v___x_4174_ = lean_apply_1(v_k_4172_, v_idx_4173_);
return v___x_4174_;
}
else
{
lean_dec(v_t_4171_);
return v_k_4172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4175_, lean_object* v_ctorIdx_4176_, lean_object* v_t_4177_, lean_object* v_h_4178_, lean_object* v_k_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4177_, v_k_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4181_, lean_object* v_ctorIdx_4182_, lean_object* v_t_4183_, lean_object* v_h_4184_, lean_object* v_k_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4181_, v_ctorIdx_4182_, v_t_4183_, v_h_4184_, v_k_4185_);
lean_dec(v_ctorIdx_4182_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4187_, lean_object* v_false_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4187_, v_false_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4190_, lean_object* v_t_4191_, lean_object* v_h_4192_, lean_object* v_false_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4191_, v_false_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4195_, lean_object* v_true_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4195_, v_true_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4198_, lean_object* v_t_4199_, lean_object* v_h_4200_, lean_object* v_true_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4199_, v_true_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4203_, lean_object* v_undef_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4203_, v_undef_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4206_, lean_object* v_t_4207_, lean_object* v_h_4208_, lean_object* v_undef_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4207_, v_undef_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4211_, lean_object* v_bvar_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4211_, v_bvar_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4214_, lean_object* v_t_4215_, lean_object* v_h_4216_, lean_object* v_bvar_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4215_, v_bvar_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4219_){
_start:
{
switch(v_x_4219_)
{
case 0:
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_box(0);
return v___x_4220_;
}
case 1:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_box(1);
return v___x_4221_;
}
default: 
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_box(2);
return v___x_4222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4223_){
_start:
{
uint8_t v_x_25__boxed_4224_; lean_object* v_res_4225_; 
v_x_25__boxed_4224_ = lean_unbox(v_x_4223_);
v_res_4225_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4224_);
return v_res_4225_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4226_){
_start:
{
switch(lean_obj_tag(v_x_4226_))
{
case 0:
{
uint8_t v___x_4227_; 
v___x_4227_ = 0;
return v___x_4227_;
}
case 1:
{
uint8_t v___x_4228_; 
v___x_4228_ = 1;
return v___x_4228_;
}
default: 
{
uint8_t v___x_4229_; 
v___x_4229_ = 2;
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4230_){
_start:
{
uint8_t v_res_4231_; lean_object* v_r_4232_; 
v_res_4231_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4230_);
lean_dec(v_x_4230_);
v_r_4232_ = lean_box(v_res_4231_);
return v_r_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4234_){
_start:
{
switch(lean_obj_tag(v_e_4234_))
{
case 3:
{
lean_object* v_u_4235_; uint8_t v___x_4236_; 
v_u_4235_ = lean_ctor_get(v_e_4234_, 0);
v___x_4236_ = l_Lean_Level_isNeverZero(v_u_4235_);
if (v___x_4236_ == 0)
{
uint8_t v___x_4237_; 
v___x_4237_ = l_Lean_Level_isZero(v_u_4235_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_box(2);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_box(1);
return v___x_4239_;
}
}
else
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_box(0);
return v___x_4240_;
}
}
case 5:
{
lean_object* v_fn_4241_; 
v_fn_4241_ = lean_ctor_get(v_e_4234_, 0);
if (lean_obj_tag(v_fn_4241_) == 4)
{
lean_object* v_declName_4242_; 
v_declName_4242_ = lean_ctor_get(v_fn_4241_, 0);
if (lean_obj_tag(v_declName_4242_) == 1)
{
lean_object* v_pre_4243_; 
v_pre_4243_ = lean_ctor_get(v_declName_4242_, 0);
if (lean_obj_tag(v_pre_4243_) == 0)
{
lean_object* v_arg_4244_; lean_object* v_str_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_arg_4244_ = lean_ctor_get(v_e_4234_, 1);
v_str_4245_ = lean_ctor_get(v_declName_4242_, 1);
v___x_4246_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4247_ = lean_string_dec_eq(v_str_4245_, v___x_4246_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; 
v___x_4248_ = lean_box(2);
return v___x_4248_;
}
else
{
v_e_4234_ = v_arg_4244_;
goto _start;
}
}
else
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_box(2);
return v___x_4250_;
}
}
else
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_box(2);
return v___x_4251_;
}
}
else
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_box(2);
return v___x_4252_;
}
}
default: 
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_box(2);
return v___x_4253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4254_);
lean_dec_ref(v_e_4254_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4256_, lean_object* v_binderType_4257_){
_start:
{
if (lean_obj_tag(v_r_4256_) == 3)
{
lean_object* v_idx_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4270_; 
v_idx_4258_ = lean_ctor_get(v_r_4256_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v_r_4256_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4260_ = v_r_4256_;
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_idx_4258_);
lean_dec(v_r_4256_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v_zero_4262_; uint8_t v_isZero_4263_; 
v_zero_4262_ = lean_unsigned_to_nat(0u);
v_isZero_4263_ = lean_nat_dec_eq(v_idx_4258_, v_zero_4262_);
if (v_isZero_4263_ == 1)
{
lean_object* v___x_4264_; 
lean_del_object(v___x_4260_);
lean_dec(v_idx_4258_);
v___x_4264_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4257_);
return v___x_4264_;
}
else
{
lean_object* v_one_4265_; lean_object* v_n_4266_; lean_object* v___x_4268_; 
v_one_4265_ = lean_unsigned_to_nat(1u);
v_n_4266_ = lean_nat_sub(v_idx_4258_, v_one_4265_);
lean_dec(v_idx_4258_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v_n_4266_);
v___x_4268_ = v___x_4260_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_n_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
return v_r_4256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4271_, lean_object* v_binderType_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4271_, v_binderType_4272_);
lean_dec_ref(v_binderType_4272_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4274_, lean_object* v_x_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_type_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; 
switch(lean_obj_tag(v_x_4274_))
{
case 7:
{
lean_object* v_binderType_4309_; lean_object* v_body_4310_; lean_object* v_zero_4311_; uint8_t v_isZero_4312_; 
v_binderType_4309_ = lean_ctor_get(v_x_4274_, 1);
v_body_4310_ = lean_ctor_get(v_x_4274_, 2);
v_zero_4311_ = lean_unsigned_to_nat(0u);
v_isZero_4312_ = lean_nat_dec_eq(v_x_4275_, v_zero_4311_);
if (v_isZero_4312_ == 1)
{
v_type_4282_ = v_x_4274_;
v___y_4283_ = v_a_4276_;
v___y_4284_ = v_a_4277_;
v___y_4285_ = v_a_4278_;
v___y_4286_ = v_a_4279_;
goto v___jp_4281_;
}
else
{
lean_object* v_one_4313_; lean_object* v_n_4314_; lean_object* v___x_4315_; 
lean_inc_ref(v_body_4310_);
lean_inc_ref(v_binderType_4309_);
lean_dec_ref_known(v_x_4274_, 3);
v_one_4313_ = lean_unsigned_to_nat(1u);
v_n_4314_ = lean_nat_sub(v_x_4275_, v_one_4313_);
v___x_4315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4310_, v_n_4314_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
lean_dec(v_n_4314_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4324_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4324_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4320_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4316_, v_binderType_4309_);
lean_dec_ref(v_binderType_4309_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4320_);
v___x_4322_ = v___x_4318_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
else
{
lean_dec_ref(v_binderType_4309_);
return v___x_4315_;
}
}
}
case 8:
{
lean_object* v_type_4325_; lean_object* v_body_4326_; lean_object* v___x_4327_; 
v_type_4325_ = lean_ctor_get(v_x_4274_, 1);
lean_inc_ref(v_type_4325_);
v_body_4326_ = lean_ctor_get(v_x_4274_, 3);
lean_inc_ref(v_body_4326_);
lean_dec_ref_known(v_x_4274_, 4);
v___x_4327_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4326_, v_x_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
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
v___x_4332_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4328_, v_type_4325_);
lean_dec_ref(v_type_4325_);
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
lean_dec_ref(v_type_4325_);
return v___x_4327_;
}
}
case 10:
{
lean_object* v_expr_4337_; 
v_expr_4337_ = lean_ctor_get(v_x_4274_, 1);
lean_inc_ref(v_expr_4337_);
lean_dec_ref_known(v_x_4274_, 2);
v_x_4274_ = v_expr_4337_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v_deBruijnIndex_4339_ = lean_ctor_get(v_x_4274_, 0);
lean_inc(v_deBruijnIndex_4339_);
lean_dec_ref_known(v_x_4274_, 1);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_nat_dec_eq(v_x_4275_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_dec(v_deBruijnIndex_4339_);
goto v___jp_4306_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4342_, 0, v_deBruijnIndex_4339_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
}
default: 
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4344_ = lean_unsigned_to_nat(0u);
v___x_4345_ = lean_nat_dec_eq(v_x_4275_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec_ref(v_x_4274_);
goto v___jp_4306_;
}
else
{
v_type_4282_ = v_x_4274_;
v___y_4283_ = v_a_4276_;
v___y_4284_ = v_a_4277_;
v___y_4285_ = v_a_4278_;
v___y_4286_ = v_a_4279_;
goto v___jp_4281_;
}
}
}
v___jp_4281_:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Meta_isPropQuick(v_type_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
uint8_t v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4292_ = lean_unbox(v_a_4288_);
lean_dec(v_a_4288_);
v___x_4293_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4292_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4298_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4287_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4287_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
v___jp_4306_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_box(2);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
return v___x_4308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4346_, lean_object* v_x_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4346_, v_x_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_x_4347_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4354_, lean_object* v_n_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4354_, v_n_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4371_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4366_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4362_);
lean_dec(v_a_4362_);
v___x_4367_ = lean_box(v___x_4366_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4367_);
v___x_4369_ = v___x_4364_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
v_a_4372_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4361_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4361_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4380_, lean_object* v_n_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4380_, v_n_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_n_4381_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4388_, lean_object* v_x_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
switch(lean_obj_tag(v_x_4388_))
{
case 4:
{
lean_object* v_declName_4395_; lean_object* v_us_4396_; lean_object* v___x_4397_; 
v_declName_4395_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_declName_4395_);
v_us_4396_ = lean_ctor_get(v_x_4388_, 1);
lean_inc(v_us_4396_);
lean_dec_ref_known(v_x_4388_, 2);
v___x_4397_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4395_, v_us_4396_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v___x_4399_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4398_, v_x_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_x_4389_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_x_4389_);
v_a_4400_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4397_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4397_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4408_; lean_object* v___x_4409_; 
v_fvarId_4408_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_fvarId_4408_);
lean_dec_ref_known(v_x_4388_, 1);
v___x_4409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4408_, v_a_4390_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4410_, v_x_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_x_4389_);
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_x_4389_);
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
case 2:
{
lean_object* v_mvarId_4420_; lean_object* v___x_4421_; 
v_mvarId_4420_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_mvarId_4420_);
lean_dec_ref_known(v_x_4388_, 1);
v___x_4421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4420_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref_known(v___x_4421_, 1);
v___x_4423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4422_, v_x_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec(v_x_4389_);
return v___x_4423_;
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_x_4389_);
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
case 5:
{
lean_object* v_fn_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v_fn_4432_ = lean_ctor_get(v_x_4388_, 0);
lean_inc_ref(v_fn_4432_);
lean_dec_ref_known(v_x_4388_, 2);
v___x_4433_ = lean_unsigned_to_nat(1u);
v___x_4434_ = lean_nat_add(v_x_4389_, v___x_4433_);
lean_dec(v_x_4389_);
v_x_4388_ = v_fn_4432_;
v_x_4389_ = v___x_4434_;
goto _start;
}
case 10:
{
lean_object* v_expr_4436_; 
v_expr_4436_ = lean_ctor_get(v_x_4388_, 1);
lean_inc_ref(v_expr_4436_);
lean_dec_ref_known(v_x_4388_, 2);
v_x_4388_ = v_expr_4436_;
goto _start;
}
case 8:
{
lean_object* v_body_4438_; 
v_body_4438_ = lean_ctor_get(v_x_4388_, 3);
lean_inc_ref(v_body_4438_);
lean_dec_ref_known(v_x_4388_, 4);
v_x_4388_ = v_body_4438_;
goto _start;
}
case 6:
{
lean_object* v_body_4440_; lean_object* v_zero_4441_; uint8_t v_isZero_4442_; 
v_body_4440_ = lean_ctor_get(v_x_4388_, 2);
lean_inc_ref(v_body_4440_);
lean_dec_ref_known(v_x_4388_, 3);
v_zero_4441_ = lean_unsigned_to_nat(0u);
v_isZero_4442_ = lean_nat_dec_eq(v_x_4389_, v_zero_4441_);
if (v_isZero_4442_ == 1)
{
lean_object* v___x_4443_; 
lean_dec(v_x_4389_);
v___x_4443_ = l_Lean_Meta_isProofQuick(v_body_4440_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
return v___x_4443_;
}
else
{
lean_object* v_one_4444_; lean_object* v_n_4445_; 
v_one_4444_ = lean_unsigned_to_nat(1u);
v_n_4445_ = lean_nat_sub(v_x_4389_, v_one_4444_);
lean_dec(v_x_4389_);
v_x_4388_ = v_body_4440_;
v_x_4389_ = v_n_4445_;
goto _start;
}
}
default: 
{
uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec(v_x_4389_);
lean_dec_ref(v_x_4388_);
v___x_4447_ = 2;
v___x_4448_ = lean_box(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
switch(lean_obj_tag(v_x_4450_))
{
case 0:
{
uint8_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
lean_dec_ref_known(v_x_4450_, 1);
v___x_4456_ = 2;
v___x_4457_ = lean_box(v___x_4456_);
v___x_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
return v___x_4458_;
}
case 1:
{
lean_object* v_fvarId_4459_; lean_object* v___x_4460_; 
v_fvarId_4459_ = lean_ctor_get(v_x_4450_, 0);
lean_inc(v_fvarId_4459_);
lean_dec_ref_known(v_x_4450_, 1);
v___x_4460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4459_, v_a_4451_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4461_, v___x_4462_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4463_;
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
v_a_4464_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4460_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4460_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4472_; lean_object* v___x_4473_; 
v_mvarId_4472_ = lean_ctor_get(v_x_4450_, 0);
lean_inc(v_mvarId_4472_);
lean_dec_ref_known(v_x_4450_, 1);
v___x_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4472_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = lean_unsigned_to_nat(0u);
v___x_4476_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4474_, v___x_4475_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4476_;
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
v_a_4477_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4473_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4473_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
case 4:
{
lean_object* v_declName_4485_; lean_object* v_us_4486_; lean_object* v___x_4487_; 
v_declName_4485_ = lean_ctor_get(v_x_4450_, 0);
lean_inc(v_declName_4485_);
v_us_4486_ = lean_ctor_get(v_x_4450_, 1);
lean_inc(v_us_4486_);
lean_dec_ref_known(v_x_4450_, 2);
v___x_4487_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4485_, v_us_4486_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
v___x_4489_ = lean_unsigned_to_nat(0u);
v___x_4490_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4488_, v___x_4489_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
v_a_4491_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4487_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4487_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
case 5:
{
lean_object* v_fn_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_fn_4499_ = lean_ctor_get(v_x_4450_, 0);
lean_inc_ref(v_fn_4499_);
lean_dec_ref_known(v_x_4450_, 2);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4499_, v___x_4500_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
return v___x_4501_;
}
case 6:
{
lean_object* v_body_4502_; 
v_body_4502_ = lean_ctor_get(v_x_4450_, 2);
lean_inc_ref(v_body_4502_);
lean_dec_ref_known(v_x_4450_, 3);
v_x_4450_ = v_body_4502_;
goto _start;
}
case 8:
{
lean_object* v_body_4504_; 
v_body_4504_ = lean_ctor_get(v_x_4450_, 3);
lean_inc_ref(v_body_4504_);
lean_dec_ref_known(v_x_4450_, 4);
v_x_4450_ = v_body_4504_;
goto _start;
}
case 10:
{
lean_object* v_expr_4506_; 
v_expr_4506_ = lean_ctor_get(v_x_4450_, 1);
lean_inc_ref(v_expr_4506_);
lean_dec_ref_known(v_x_4450_, 2);
v_x_4450_ = v_expr_4506_;
goto _start;
}
case 11:
{
uint8_t v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref_known(v_x_4450_, 3);
v___x_4508_ = 2;
v___x_4509_ = lean_box(v___x_4508_);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
default: 
{
uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
lean_dec_ref(v_x_4450_);
v___x_4511_ = 0;
v___x_4512_ = lean_box(v___x_4511_);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
return v___x_4513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Meta_isProofQuick(v_x_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4521_, lean_object* v_x_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4521_, v_x_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; 
lean_inc_ref(v_e_4529_);
v___x_4535_ = l_Lean_Meta_isProofQuick(v_e_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4562_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4538_ = v___x_4535_;
v_isShared_4539_ = v_isSharedCheck_4562_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4535_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4562_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
uint8_t v___x_4540_; 
v___x_4540_ = lean_unbox(v_a_4536_);
lean_dec(v_a_4536_);
switch(v___x_4540_)
{
case 0:
{
uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
lean_dec_ref(v_e_4529_);
v___x_4541_ = 0;
v___x_4542_ = lean_box(v___x_4541_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4542_);
v___x_4544_ = v___x_4538_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
case 1:
{
uint8_t v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
lean_dec_ref(v_e_4529_);
v___x_4546_ = 1;
v___x_4547_ = lean_box(v___x_4546_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4547_);
v___x_4549_ = v___x_4538_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
default: 
{
lean_object* v___x_4551_; 
lean_del_object(v___x_4538_);
lean_inc(v_a_4533_);
lean_inc_ref(v_a_4532_);
lean_inc(v_a_4531_);
lean_inc_ref(v_a_4530_);
v___x_4551_ = lean_infer_type(v_e_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4553_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v___x_4553_ = l_Lean_Meta_isProp(v_a_4552_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4553_;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
v_a_4554_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4551_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4551_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v_e_4529_);
v_a_4563_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4535_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4535_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Meta_isProof(v_e_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4578_, lean_object* v_x_4579_){
_start:
{
switch(lean_obj_tag(v_x_4578_))
{
case 3:
{
lean_object* v___x_4585_; uint8_t v___x_4586_; 
v___x_4585_ = lean_unsigned_to_nat(0u);
v___x_4586_ = lean_nat_dec_eq(v_x_4579_, v___x_4585_);
lean_dec(v_x_4579_);
if (v___x_4586_ == 0)
{
goto v___jp_4581_;
}
else
{
uint8_t v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = 1;
v___x_4588_ = lean_box(v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
case 7:
{
lean_object* v_body_4590_; lean_object* v_zero_4591_; uint8_t v_isZero_4592_; 
v_body_4590_ = lean_ctor_get(v_x_4578_, 2);
v_zero_4591_ = lean_unsigned_to_nat(0u);
v_isZero_4592_ = lean_nat_dec_eq(v_x_4579_, v_zero_4591_);
if (v_isZero_4592_ == 1)
{
uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_dec(v_x_4579_);
v___x_4593_ = 0;
v___x_4594_ = lean_box(v___x_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
else
{
lean_object* v_one_4596_; lean_object* v_n_4597_; 
v_one_4596_ = lean_unsigned_to_nat(1u);
v_n_4597_ = lean_nat_sub(v_x_4579_, v_one_4596_);
lean_dec(v_x_4579_);
v_x_4578_ = v_body_4590_;
v_x_4579_ = v_n_4597_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4599_; 
v_body_4599_ = lean_ctor_get(v_x_4578_, 3);
v_x_4578_ = v_body_4599_;
goto _start;
}
case 10:
{
lean_object* v_expr_4601_; 
v_expr_4601_ = lean_ctor_get(v_x_4578_, 1);
v_x_4578_ = v_expr_4601_;
goto _start;
}
default: 
{
lean_dec(v_x_4579_);
goto v___jp_4581_;
}
}
v___jp_4581_:
{
uint8_t v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = 2;
v___x_4583_ = lean_box(v___x_4582_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4603_, lean_object* v_x_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4603_, v_x_4604_);
lean_dec_ref(v_x_4603_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4607_, lean_object* v_x_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4607_, v_x_4608_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4615_, lean_object* v_x_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4615_, v_x_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec_ref(v_x_4615_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4623_, lean_object* v_x_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
switch(lean_obj_tag(v_x_4623_))
{
case 4:
{
lean_object* v_declName_4630_; lean_object* v_us_4631_; lean_object* v___x_4632_; 
v_declName_4630_ = lean_ctor_get(v_x_4623_, 0);
lean_inc(v_declName_4630_);
v_us_4631_ = lean_ctor_get(v_x_4623_, 1);
lean_inc(v_us_4631_);
lean_dec_ref_known(v_x_4623_, 2);
v___x_4632_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4630_, v_us_4631_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4634_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v___x_4634_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4633_, v_x_4624_);
lean_dec(v_a_4633_);
return v___x_4634_;
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec(v_x_4624_);
v_a_4635_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4632_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4632_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4643_; lean_object* v___x_4644_; 
v_fvarId_4643_ = lean_ctor_get(v_x_4623_, 0);
lean_inc(v_fvarId_4643_);
lean_dec_ref_known(v_x_4623_, 1);
v___x_4644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4643_, v_a_4625_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4645_, v_x_4624_);
lean_dec(v_a_4645_);
return v___x_4646_;
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_x_4624_);
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
case 2:
{
lean_object* v_mvarId_4655_; lean_object* v___x_4656_; 
v_mvarId_4655_ = lean_ctor_get(v_x_4623_, 0);
lean_inc(v_mvarId_4655_);
lean_dec_ref_known(v_x_4623_, 1);
v___x_4656_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4655_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref_known(v___x_4656_, 1);
v___x_4658_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4657_, v_x_4624_);
lean_dec(v_a_4657_);
return v___x_4658_;
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v_x_4624_);
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
case 5:
{
lean_object* v_fn_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v_fn_4667_ = lean_ctor_get(v_x_4623_, 0);
lean_inc_ref(v_fn_4667_);
lean_dec_ref_known(v_x_4623_, 2);
v___x_4668_ = lean_unsigned_to_nat(1u);
v___x_4669_ = lean_nat_add(v_x_4624_, v___x_4668_);
lean_dec(v_x_4624_);
v_x_4623_ = v_fn_4667_;
v_x_4624_ = v___x_4669_;
goto _start;
}
case 10:
{
lean_object* v_expr_4671_; 
v_expr_4671_ = lean_ctor_get(v_x_4623_, 1);
lean_inc_ref(v_expr_4671_);
lean_dec_ref_known(v_x_4623_, 2);
v_x_4623_ = v_expr_4671_;
goto _start;
}
case 8:
{
lean_object* v_body_4673_; 
v_body_4673_ = lean_ctor_get(v_x_4623_, 3);
lean_inc_ref(v_body_4673_);
lean_dec_ref_known(v_x_4623_, 4);
v_x_4623_ = v_body_4673_;
goto _start;
}
case 6:
{
lean_object* v_body_4675_; lean_object* v_zero_4676_; uint8_t v_isZero_4677_; 
v_body_4675_ = lean_ctor_get(v_x_4623_, 2);
lean_inc_ref(v_body_4675_);
lean_dec_ref_known(v_x_4623_, 3);
v_zero_4676_ = lean_unsigned_to_nat(0u);
v_isZero_4677_ = lean_nat_dec_eq(v_x_4624_, v_zero_4676_);
if (v_isZero_4677_ == 1)
{
uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
lean_dec_ref(v_body_4675_);
lean_dec(v_x_4624_);
v___x_4678_ = 0;
v___x_4679_ = lean_box(v___x_4678_);
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
return v___x_4680_;
}
else
{
lean_object* v_one_4681_; lean_object* v_n_4682_; 
v_one_4681_ = lean_unsigned_to_nat(1u);
v_n_4682_ = lean_nat_sub(v_x_4624_, v_one_4681_);
lean_dec(v_x_4624_);
v_x_4623_ = v_body_4675_;
v_x_4624_ = v_n_4682_;
goto _start;
}
}
default: 
{
uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
lean_dec(v_x_4624_);
lean_dec_ref(v_x_4623_);
v___x_4684_ = 2;
v___x_4685_ = lean_box(v___x_4684_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4687_, lean_object* v_x_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4687_, v_x_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
switch(lean_obj_tag(v_x_4695_))
{
case 1:
{
lean_object* v_fvarId_4701_; lean_object* v___x_4702_; 
v_fvarId_4701_ = lean_ctor_get(v_x_4695_, 0);
lean_inc(v_fvarId_4701_);
lean_dec_ref_known(v_x_4695_, 1);
v___x_4702_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4701_, v_a_4696_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4702_, 1);
v___x_4704_ = lean_unsigned_to_nat(0u);
v___x_4705_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4703_, v___x_4704_);
lean_dec(v_a_4703_);
return v___x_4705_;
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
v_a_4706_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4702_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4702_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4714_; lean_object* v___x_4715_; 
v_mvarId_4714_ = lean_ctor_get(v_x_4695_, 0);
lean_inc(v_mvarId_4714_);
lean_dec_ref_known(v_x_4695_, 1);
v___x_4715_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4714_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4716_, v___x_4717_);
lean_dec(v_a_4716_);
return v___x_4718_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
v_a_4719_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4715_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4715_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
case 3:
{
uint8_t v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
lean_dec_ref_known(v_x_4695_, 1);
v___x_4727_ = 1;
v___x_4728_ = lean_box(v___x_4727_);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
return v___x_4729_;
}
case 4:
{
lean_object* v_declName_4730_; lean_object* v_us_4731_; lean_object* v___x_4732_; 
v_declName_4730_ = lean_ctor_get(v_x_4695_, 0);
lean_inc(v_declName_4730_);
v_us_4731_ = lean_ctor_get(v_x_4695_, 1);
lean_inc(v_us_4731_);
lean_dec_ref_known(v_x_4695_, 2);
v___x_4732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4730_, v_us_4731_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4732_, 1);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4733_, v___x_4734_);
lean_dec(v_a_4733_);
return v___x_4735_;
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
v_a_4736_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4732_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4732_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
case 5:
{
lean_object* v_fn_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v_fn_4744_ = lean_ctor_get(v_x_4695_, 0);
lean_inc_ref(v_fn_4744_);
lean_dec_ref_known(v_x_4695_, 2);
v___x_4745_ = lean_unsigned_to_nat(1u);
v___x_4746_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4744_, v___x_4745_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
return v___x_4746_;
}
case 6:
{
uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_dec_ref_known(v_x_4695_, 3);
v___x_4747_ = 0;
v___x_4748_ = lean_box(v___x_4747_);
v___x_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
return v___x_4749_;
}
case 7:
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_dec_ref_known(v_x_4695_, 3);
v___x_4750_ = 1;
v___x_4751_ = lean_box(v___x_4750_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
case 8:
{
lean_object* v_body_4753_; 
v_body_4753_ = lean_ctor_get(v_x_4695_, 3);
lean_inc_ref(v_body_4753_);
lean_dec_ref_known(v_x_4695_, 4);
v_x_4695_ = v_body_4753_;
goto _start;
}
case 9:
{
uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
lean_dec_ref_known(v_x_4695_, 1);
v___x_4755_ = 0;
v___x_4756_ = lean_box(v___x_4755_);
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
return v___x_4757_;
}
case 10:
{
lean_object* v_expr_4758_; 
v_expr_4758_ = lean_ctor_get(v_x_4695_, 1);
lean_inc_ref(v_expr_4758_);
lean_dec_ref_known(v_x_4695_, 2);
v_x_4695_ = v_expr_4758_;
goto _start;
}
default: 
{
uint8_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec_ref(v_x_4695_);
v___x_4760_ = 2;
v___x_4761_ = lean_box(v___x_4760_);
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_Meta_isTypeQuick(v_x_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v___x_4776_; 
lean_inc_ref(v_e_4770_);
v___x_4776_ = l_Lean_Meta_isTypeQuick(v_e_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4826_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4826_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4826_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
uint8_t v___x_4781_; 
v___x_4781_ = lean_unbox(v_a_4777_);
lean_dec(v_a_4777_);
switch(v___x_4781_)
{
case 0:
{
uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
lean_dec_ref(v_e_4770_);
v___x_4782_ = 0;
v___x_4783_ = lean_box(v___x_4782_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4783_);
v___x_4785_ = v___x_4779_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
case 1:
{
uint8_t v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4790_; 
lean_dec_ref(v_e_4770_);
v___x_4787_ = 1;
v___x_4788_ = lean_box(v___x_4787_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4788_);
v___x_4790_ = v___x_4779_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
default: 
{
lean_object* v___x_4792_; 
lean_del_object(v___x_4779_);
lean_inc(v_a_4774_);
lean_inc_ref(v_a_4773_);
lean_inc(v_a_4772_);
lean_inc_ref(v_a_4771_);
v___x_4792_ = lean_infer_type(v_e_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4794_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v___x_4792_, 1);
v___x_4794_ = l_Lean_Meta_whnfD(v_a_4793_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4809_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4797_ = v___x_4794_;
v_isShared_4798_ = v_isSharedCheck_4809_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4794_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4809_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
if (lean_obj_tag(v_a_4795_) == 3)
{
uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
lean_dec_ref_known(v_a_4795_, 1);
v___x_4799_ = 1;
v___x_4800_ = lean_box(v___x_4799_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4800_);
v___x_4802_ = v___x_4797_;
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
else
{
uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
lean_dec(v_a_4795_);
v___x_4804_ = 0;
v___x_4805_ = lean_box(v___x_4804_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 0, v___x_4805_);
v___x_4807_ = v___x_4797_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
v_a_4810_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4794_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4794_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4792_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4792_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec_ref(v_e_4770_);
v_a_4827_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4776_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4776_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_isType(v_e_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4842_){
_start:
{
switch(lean_obj_tag(v_x_4842_))
{
case 7:
{
lean_object* v_body_4843_; 
v_body_4843_ = lean_ctor_get(v_x_4842_, 2);
v_x_4842_ = v_body_4843_;
goto _start;
}
case 3:
{
lean_object* v_u_4845_; lean_object* v___x_4846_; 
v_u_4845_ = lean_ctor_get(v_x_4842_, 0);
lean_inc(v_u_4845_);
v___x_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4846_, 0, v_u_4845_);
return v___x_4846_;
}
default: 
{
lean_object* v___x_4847_; 
v___x_4847_ = lean_box(0);
return v___x_4847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4848_);
lean_dec_ref(v_x_4848_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4850_, lean_object* v_body_4851_, lean_object* v_x_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4850_, v_body_4851_, v_x_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4861_, lean_object* v_xs_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
switch(lean_obj_tag(v_type_4861_))
{
case 3:
{
lean_object* v_u_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
lean_dec_ref(v_xs_4862_);
v_u_4868_ = lean_ctor_get(v_type_4861_, 0);
lean_inc(v_u_4868_);
lean_dec_ref_known(v_type_4861_, 1);
v___x_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_u_4868_);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
return v___x_4870_;
}
case 7:
{
lean_object* v_binderName_4871_; lean_object* v_binderType_4872_; lean_object* v_body_4873_; uint8_t v_binderInfo_4874_; lean_object* v___f_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v_binderName_4871_ = lean_ctor_get(v_type_4861_, 0);
lean_inc(v_binderName_4871_);
v_binderType_4872_ = lean_ctor_get(v_type_4861_, 1);
lean_inc_ref(v_binderType_4872_);
v_body_4873_ = lean_ctor_get(v_type_4861_, 2);
lean_inc_ref(v_body_4873_);
v_binderInfo_4874_ = lean_ctor_get_uint8(v_type_4861_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4861_, 3);
lean_inc_ref(v_xs_4862_);
v___f_4875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4875_, 0, v_xs_4862_);
lean_closure_set(v___f_4875_, 1, v_body_4873_);
v___x_4876_ = lean_expr_instantiate_rev(v_binderType_4872_, v_xs_4862_);
lean_dec_ref(v_xs_4862_);
lean_dec_ref(v_binderType_4872_);
v___x_4877_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4871_, v_binderInfo_4874_, v___x_4876_, v___f_4875_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
return v___x_4877_;
}
default: 
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = lean_expr_instantiate_rev(v_type_4861_, v_xs_4862_);
lean_dec_ref(v_xs_4862_);
lean_dec_ref(v_type_4861_);
v___x_4879_ = l_Lean_Meta_whnfD(v___x_4878_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4895_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4895_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4895_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
switch(lean_obj_tag(v_a_4880_))
{
case 3:
{
lean_object* v_u_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v_u_4884_ = lean_ctor_get(v_a_4880_, 0);
lean_inc(v_u_4884_);
lean_dec_ref_known(v_a_4880_, 1);
v___x_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_u_4884_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4885_);
v___x_4887_ = v___x_4882_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
case 7:
{
lean_object* v___x_4889_; 
lean_del_object(v___x_4882_);
v___x_4889_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4861_ = v_a_4880_;
v_xs_4862_ = v___x_4889_;
goto _start;
}
default: 
{
lean_object* v___x_4891_; lean_object* v___x_4893_; 
lean_dec(v_a_4880_);
v___x_4891_ = lean_box(0);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4891_);
v___x_4893_ = v___x_4882_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4879_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4879_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4904_, lean_object* v_body_4905_, lean_object* v_x_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_array_push(v_xs_4904_, v_x_4906_);
v___x_4913_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4905_, v___x_4912_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4914_, lean_object* v_xs_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4914_, v_xs_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4922_, lean_object* v_cache_4923_, lean_object* v_a_x3f_4924_){
_start:
{
lean_object* v___x_4926_; lean_object* v_mctx_4927_; lean_object* v_zetaDeltaFVarIds_4928_; lean_object* v_postponed_4929_; lean_object* v_diag_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4940_; 
v___x_4926_ = lean_st_ref_take(v_a_4922_);
v_mctx_4927_ = lean_ctor_get(v___x_4926_, 0);
v_zetaDeltaFVarIds_4928_ = lean_ctor_get(v___x_4926_, 2);
v_postponed_4929_ = lean_ctor_get(v___x_4926_, 3);
v_diag_4930_ = lean_ctor_get(v___x_4926_, 4);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4940_ == 0)
{
lean_object* v_unused_4941_; 
v_unused_4941_ = lean_ctor_get(v___x_4926_, 1);
lean_dec(v_unused_4941_);
v___x_4932_ = v___x_4926_;
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_diag_4930_);
lean_inc(v_postponed_4929_);
lean_inc(v_zetaDeltaFVarIds_4928_);
lean_inc(v_mctx_4927_);
lean_dec(v___x_4926_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v_cache_4923_);
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_mctx_4927_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_cache_4923_);
lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_zetaDeltaFVarIds_4928_);
lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_postponed_4929_);
lean_ctor_set(v_reuseFailAlloc_4939_, 4, v_diag_4930_);
v___x_4935_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = lean_st_ref_put(v_a_4922_, v___x_4935_);
v___x_4937_ = lean_box(0);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
return v___x_4938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4942_, lean_object* v_cache_4943_, lean_object* v_a_x3f_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4942_, v_cache_4943_, v_a_x3f_4944_);
lean_dec(v_a_x3f_4944_);
lean_dec(v_a_4942_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4947_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; lean_object* v_cache_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4954_ = lean_st_ref_get(v_a_4949_);
v_cache_4955_ = lean_ctor_get(v___x_4954_, 1);
lean_inc_ref(v_cache_4955_);
lean_dec(v___x_4954_);
v___x_4956_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4947_, v___x_4956_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4974_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_4974_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4974_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
lean_inc(v_a_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set_tag(v___x_4960_, 1);
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
v___x_4964_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4949_, v_cache_4955_, v___x_4963_);
lean_dec_ref(v___x_4963_);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4971_ == 0)
{
lean_object* v_unused_4972_; 
v_unused_4972_ = lean_ctor_get(v___x_4964_, 0);
lean_dec(v_unused_4972_);
v___x_4966_ = v___x_4964_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_dec(v___x_4964_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v_a_4958_);
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4958_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
v_a_4975_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4976_ = lean_box(0);
v___x_4977_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4949_, v_cache_4955_, v___x_4976_);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4984_ == 0)
{
lean_object* v_unused_4985_; 
v_unused_4985_ = lean_ctor_get(v___x_4977_, 0);
lean_dec(v_unused_4985_);
v___x_4979_ = v___x_4977_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_dec(v___x_4977_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set_tag(v___x_4979_, 1);
lean_ctor_set(v___x_4979_, 0, v_a_4975_);
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4975_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
else
{
lean_object* v___x_4986_; 
lean_dec_ref(v_type_4947_);
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4953_);
return v___x_4986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5015_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5003_ = v___x_5000_;
v_isShared_5004_ = v_isSharedCheck_5015_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_5000_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5015_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
if (lean_obj_tag(v_a_5001_) == 0)
{
uint8_t v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5008_; 
v___x_5005_ = 0;
v___x_5006_ = lean_box(v___x_5005_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 0, v___x_5006_);
v___x_5008_ = v___x_5003_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5006_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
else
{
uint8_t v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5013_; 
lean_dec_ref_known(v_a_5001_, 1);
v___x_5010_ = 1;
v___x_5011_ = lean_box(v___x_5010_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 0, v___x_5011_);
v___x_5013_ = v___x_5003_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5000_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5000_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l_Lean_Meta_isTypeFormerType(v_type_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
return v_res_5030_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5031_, lean_object* v_x_5032_){
_start:
{
if (lean_obj_tag(v_x_5031_) == 0)
{
if (lean_obj_tag(v_x_5032_) == 0)
{
uint8_t v___x_5033_; 
v___x_5033_ = 1;
return v___x_5033_;
}
else
{
uint8_t v___x_5034_; 
v___x_5034_ = 0;
return v___x_5034_;
}
}
else
{
if (lean_obj_tag(v_x_5032_) == 0)
{
uint8_t v___x_5035_; 
v___x_5035_ = 0;
return v___x_5035_;
}
else
{
lean_object* v_val_5036_; lean_object* v_val_5037_; uint8_t v___x_5038_; 
v_val_5036_ = lean_ctor_get(v_x_5031_, 0);
v_val_5037_ = lean_ctor_get(v_x_5032_, 0);
v___x_5038_ = lean_level_eq(v_val_5036_, v_val_5037_);
return v___x_5038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5039_, lean_object* v_x_5040_){
_start:
{
uint8_t v_res_5041_; lean_object* v_r_5042_; 
v_res_5041_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5039_, v_x_5040_);
lean_dec(v_x_5040_);
lean_dec(v_x_5039_);
v_r_5042_ = lean_box(v_res_5041_);
return v_r_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5062_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5054_ = v___x_5051_;
v_isShared_5055_ = v_isSharedCheck_5062_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5051_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5062_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; uint8_t v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5060_; 
v___x_5056_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5057_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5052_, v___x_5056_);
lean_dec(v_a_5052_);
v___x_5058_ = lean_box(v___x_5057_);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5058_);
v___x_5060_ = v___x_5054_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
v_a_5063_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_5051_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5051_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_Meta_isPropFormerType(v_type_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v___x_5084_; 
lean_inc(v_a_5082_);
lean_inc_ref(v_a_5081_);
lean_inc(v_a_5080_);
lean_inc_ref(v_a_5079_);
v___x_5084_ = lean_infer_type(v_e_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5086_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v___x_5086_ = l_Lean_Meta_isTypeFormerType(v_a_5085_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_);
return v___x_5086_;
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
v_a_5087_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5084_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5084_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Meta_isTypeFormer(v_e_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5102_, lean_object* v_maxFVars_x3f_5103_, lean_object* v_k_5104_, uint8_t v_cleanupAnnotations_5105_, uint8_t v_whnfType_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v___f_5112_; lean_object* v___x_5113_; 
v___f_5112_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5112_, 0, v_k_5104_);
v___x_5113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5102_, v_maxFVars_x3f_5103_, v___f_5112_, v_cleanupAnnotations_5105_, v_whnfType_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
v_a_5122_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5113_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5113_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5130_, lean_object* v_maxFVars_x3f_5131_, lean_object* v_k_5132_, lean_object* v_cleanupAnnotations_5133_, lean_object* v_whnfType_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5140_; uint8_t v_whnfType_boxed_5141_; lean_object* v_res_5142_; 
v_cleanupAnnotations_boxed_5140_ = lean_unbox(v_cleanupAnnotations_5133_);
v_whnfType_boxed_5141_ = lean_unbox(v_whnfType_5134_);
v_res_5142_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5130_, v_maxFVars_x3f_5131_, v_k_5132_, v_cleanupAnnotations_boxed_5140_, v_whnfType_boxed_5141_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5143_, lean_object* v_type_5144_, lean_object* v_maxFVars_x3f_5145_, lean_object* v_k_5146_, uint8_t v_cleanupAnnotations_5147_, uint8_t v_whnfType_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5144_, v_maxFVars_x3f_5145_, v_k_5146_, v_cleanupAnnotations_5147_, v_whnfType_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5155_, lean_object* v_type_5156_, lean_object* v_maxFVars_x3f_5157_, lean_object* v_k_5158_, lean_object* v_cleanupAnnotations_5159_, lean_object* v_whnfType_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5166_; uint8_t v_whnfType_boxed_5167_; lean_object* v_res_5168_; 
v_cleanupAnnotations_boxed_5166_ = lean_unbox(v_cleanupAnnotations_5159_);
v_whnfType_boxed_5167_ = lean_unbox(v_whnfType_5160_);
v_res_5168_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5155_, v_type_5156_, v_maxFVars_x3f_5157_, v_k_5158_, v_cleanupAnnotations_boxed_5166_, v_whnfType_boxed_5167_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v_res_5168_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5169_, lean_object* v_as_5170_, size_t v_i_5171_, size_t v_stop_5172_){
_start:
{
uint8_t v___x_5173_; 
v___x_5173_ = lean_usize_dec_eq(v_i_5171_, v_stop_5172_);
if (v___x_5173_ == 0)
{
lean_object* v___x_5174_; uint8_t v___x_5175_; 
v___x_5174_ = lean_array_uget_borrowed(v_as_5170_, v_i_5171_);
v___x_5175_ = lean_expr_eqv(v_a_5169_, v___x_5174_);
if (v___x_5175_ == 0)
{
size_t v___x_5176_; size_t v___x_5177_; 
v___x_5176_ = ((size_t)1ULL);
v___x_5177_ = lean_usize_add(v_i_5171_, v___x_5176_);
v_i_5171_ = v___x_5177_;
goto _start;
}
else
{
return v___x_5175_;
}
}
else
{
uint8_t v___x_5179_; 
v___x_5179_ = 0;
return v___x_5179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5180_, lean_object* v_as_5181_, lean_object* v_i_5182_, lean_object* v_stop_5183_){
_start:
{
size_t v_i_boxed_5184_; size_t v_stop_boxed_5185_; uint8_t v_res_5186_; lean_object* v_r_5187_; 
v_i_boxed_5184_ = lean_unbox_usize(v_i_5182_);
lean_dec(v_i_5182_);
v_stop_boxed_5185_ = lean_unbox_usize(v_stop_5183_);
lean_dec(v_stop_5183_);
v_res_5186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5180_, v_as_5181_, v_i_boxed_5184_, v_stop_boxed_5185_);
lean_dec_ref(v_as_5181_);
lean_dec_ref(v_a_5180_);
v_r_5187_ = lean_box(v_res_5186_);
return v_r_5187_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5188_, lean_object* v_a_5189_){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; uint8_t v___x_5192_; 
v___x_5190_ = lean_unsigned_to_nat(0u);
v___x_5191_ = lean_array_get_size(v_as_5188_);
v___x_5192_ = lean_nat_dec_lt(v___x_5190_, v___x_5191_);
if (v___x_5192_ == 0)
{
return v___x_5192_;
}
else
{
if (v___x_5192_ == 0)
{
return v___x_5192_;
}
else
{
size_t v___x_5193_; size_t v___x_5194_; uint8_t v___x_5195_; 
v___x_5193_ = ((size_t)0ULL);
v___x_5194_ = lean_usize_of_nat(v___x_5191_);
v___x_5195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5189_, v_as_5188_, v___x_5193_, v___x_5194_);
return v___x_5195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5196_, lean_object* v_a_5197_){
_start:
{
uint8_t v_res_5198_; lean_object* v_r_5199_; 
v_res_5198_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5196_, v_a_5197_);
lean_dec_ref(v_a_5197_);
lean_dec_ref(v_as_5196_);
v_r_5199_ = lean_box(v_res_5198_);
return v_r_5199_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5200_, lean_object* v_e_5201_){
_start:
{
uint8_t v___x_5202_; lean_object* v_d_5204_; lean_object* v_b_5205_; 
v___x_5202_ = l_Lean_Expr_hasFVar(v_e_5201_);
if (v___x_5202_ == 0)
{
lean_dec_ref(v_e_5201_);
return v___x_5202_;
}
else
{
switch(lean_obj_tag(v_e_5201_))
{
case 7:
{
lean_object* v_binderType_5208_; lean_object* v_body_5209_; 
v_binderType_5208_ = lean_ctor_get(v_e_5201_, 1);
lean_inc_ref(v_binderType_5208_);
v_body_5209_ = lean_ctor_get(v_e_5201_, 2);
lean_inc_ref(v_body_5209_);
lean_dec_ref_known(v_e_5201_, 3);
v_d_5204_ = v_binderType_5208_;
v_b_5205_ = v_body_5209_;
goto v___jp_5203_;
}
case 6:
{
lean_object* v_binderType_5210_; lean_object* v_body_5211_; 
v_binderType_5210_ = lean_ctor_get(v_e_5201_, 1);
lean_inc_ref(v_binderType_5210_);
v_body_5211_ = lean_ctor_get(v_e_5201_, 2);
lean_inc_ref(v_body_5211_);
lean_dec_ref_known(v_e_5201_, 3);
v_d_5204_ = v_binderType_5210_;
v_b_5205_ = v_body_5211_;
goto v___jp_5203_;
}
case 10:
{
lean_object* v_expr_5212_; 
v_expr_5212_ = lean_ctor_get(v_e_5201_, 1);
lean_inc_ref(v_expr_5212_);
lean_dec_ref_known(v_e_5201_, 2);
v_e_5201_ = v_expr_5212_;
goto _start;
}
case 8:
{
lean_object* v_type_5214_; lean_object* v_value_5215_; lean_object* v_body_5216_; uint8_t v___x_5217_; 
v_type_5214_ = lean_ctor_get(v_e_5201_, 1);
lean_inc_ref(v_type_5214_);
v_value_5215_ = lean_ctor_get(v_e_5201_, 2);
lean_inc_ref(v_value_5215_);
v_body_5216_ = lean_ctor_get(v_e_5201_, 3);
lean_inc_ref(v_body_5216_);
lean_dec_ref_known(v_e_5201_, 4);
v___x_5217_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5200_, v_type_5214_);
if (v___x_5217_ == 0)
{
uint8_t v___x_5218_; 
v___x_5218_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5200_, v_value_5215_);
if (v___x_5218_ == 0)
{
v_e_5201_ = v_body_5216_;
goto _start;
}
else
{
lean_dec_ref(v_body_5216_);
return v___x_5202_;
}
}
else
{
lean_dec_ref(v_body_5216_);
lean_dec_ref(v_value_5215_);
return v___x_5202_;
}
}
case 5:
{
lean_object* v_fn_5220_; lean_object* v_arg_5221_; uint8_t v___x_5222_; 
v_fn_5220_ = lean_ctor_get(v_e_5201_, 0);
lean_inc_ref(v_fn_5220_);
v_arg_5221_ = lean_ctor_get(v_e_5201_, 1);
lean_inc_ref(v_arg_5221_);
lean_dec_ref_known(v_e_5201_, 2);
v___x_5222_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5200_, v_fn_5220_);
if (v___x_5222_ == 0)
{
v_e_5201_ = v_arg_5221_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5221_);
return v___x_5202_;
}
}
case 11:
{
lean_object* v_struct_5224_; 
v_struct_5224_ = lean_ctor_get(v_e_5201_, 2);
lean_inc_ref(v_struct_5224_);
lean_dec_ref_known(v_e_5201_, 3);
v_e_5201_ = v_struct_5224_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5226_; lean_object* v___x_5227_; uint8_t v___x_5228_; 
v_fvarId_5226_ = lean_ctor_get(v_e_5201_, 0);
lean_inc(v_fvarId_5226_);
lean_dec_ref_known(v_e_5201_, 1);
v___x_5227_ = l_Lean_Expr_fvar___override(v_fvarId_5226_);
v___x_5228_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5200_, v___x_5227_);
lean_dec_ref(v___x_5227_);
return v___x_5228_;
}
default: 
{
uint8_t v___x_5229_; 
lean_dec_ref(v_e_5201_);
v___x_5229_ = 0;
return v___x_5229_;
}
}
}
v___jp_5203_:
{
uint8_t v___x_5206_; 
v___x_5206_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5200_, v_d_5204_);
if (v___x_5206_ == 0)
{
v_e_5201_ = v_b_5205_;
goto _start;
}
else
{
lean_dec_ref(v_b_5205_);
return v___x_5202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5230_, lean_object* v_e_5231_){
_start:
{
uint8_t v_res_5232_; lean_object* v_r_5233_; 
v_res_5232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5230_, v_e_5231_);
lean_dec_ref(v_xs_5230_);
v_r_5233_ = lean_box(v_res_5232_);
return v_r_5233_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5236_ = l_Lean_stringToMessageData(v___x_5235_);
return v___x_5236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5239_ = l_Lean_stringToMessageData(v___x_5238_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5240_, lean_object* v_type_5241_, lean_object* v_as_5242_, size_t v_sz_5243_, size_t v_i_5244_, lean_object* v_b_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v_a_5252_; uint8_t v___x_5256_; 
v___x_5256_ = lean_usize_dec_lt(v_i_5244_, v_sz_5243_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; 
lean_dec_ref(v_type_5241_);
v___x_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5257_, 0, v_b_5245_);
return v___x_5257_;
}
else
{
lean_object* v___x_5258_; lean_object* v_a_5259_; uint8_t v___x_5260_; 
v___x_5258_ = lean_box(0);
v_a_5259_ = lean_array_uget_borrowed(v_as_5242_, v_i_5244_);
lean_inc(v_a_5259_);
v___x_5260_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5240_, v_a_5259_);
if (v___x_5260_ == 0)
{
v_a_5252_ = v___x_5258_;
goto v___jp_5251_;
}
else
{
lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5259_);
v___x_5262_ = l_Lean_MessageData_ofExpr(v_a_5259_);
v___x_5263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5261_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
v___x_5264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5263_);
lean_ctor_set(v___x_5265_, 1, v___x_5264_);
lean_inc_ref(v_type_5241_);
v___x_5266_ = l_Lean_MessageData_ofExpr(v_type_5241_);
v___x_5267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5265_);
lean_ctor_set(v___x_5267_, 1, v___x_5266_);
v___x_5268_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5267_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_dec_ref_known(v___x_5268_, 1);
v_a_5252_ = v___x_5258_;
goto v___jp_5251_;
}
else
{
lean_dec_ref(v_type_5241_);
return v___x_5268_;
}
}
}
v___jp_5251_:
{
size_t v___x_5253_; size_t v___x_5254_; 
v___x_5253_ = ((size_t)1ULL);
v___x_5254_ = lean_usize_add(v_i_5244_, v___x_5253_);
v_i_5244_ = v___x_5254_;
v_b_5245_ = v_a_5252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5269_, lean_object* v_type_5270_, lean_object* v_as_5271_, lean_object* v_sz_5272_, lean_object* v_i_5273_, lean_object* v_b_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
size_t v_sz_boxed_5280_; size_t v_i_boxed_5281_; lean_object* v_res_5282_; 
v_sz_boxed_5280_ = lean_unbox_usize(v_sz_5272_);
lean_dec(v_sz_5272_);
v_i_boxed_5281_ = lean_unbox_usize(v_i_5273_);
lean_dec(v_i_5273_);
v_res_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5269_, v_type_5270_, v_as_5271_, v_sz_boxed_5280_, v_i_boxed_5281_, v_b_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec_ref(v_as_5271_);
lean_dec_ref(v_xs_5269_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5283_, size_t v_i_5284_, lean_object* v_bs_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
uint8_t v___x_5291_; 
v___x_5291_ = lean_usize_dec_lt(v_i_5284_, v_sz_5283_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5292_; 
v___x_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5292_, 0, v_bs_5285_);
return v___x_5292_;
}
else
{
lean_object* v_v_5293_; lean_object* v___x_5294_; 
v_v_5293_ = lean_array_uget_borrowed(v_bs_5285_, v_i_5284_);
lean_inc(v___y_5289_);
lean_inc_ref(v___y_5288_);
lean_inc(v___y_5287_);
lean_inc_ref(v___y_5286_);
lean_inc(v_v_5293_);
v___x_5294_ = lean_infer_type(v_v_5293_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5296_; lean_object* v_bs_x27_5297_; size_t v___x_5298_; size_t v___x_5299_; lean_object* v___x_5300_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref_known(v___x_5294_, 1);
v___x_5296_ = lean_unsigned_to_nat(0u);
v_bs_x27_5297_ = lean_array_uset(v_bs_5285_, v_i_5284_, v___x_5296_);
v___x_5298_ = ((size_t)1ULL);
v___x_5299_ = lean_usize_add(v_i_5284_, v___x_5298_);
v___x_5300_ = lean_array_uset(v_bs_x27_5297_, v_i_5284_, v_a_5295_);
v_i_5284_ = v___x_5299_;
v_bs_5285_ = v___x_5300_;
goto _start;
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec_ref(v_bs_5285_);
v_a_5302_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5294_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5294_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5310_, lean_object* v_i_5311_, lean_object* v_bs_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
size_t v_sz_boxed_5318_; size_t v_i_boxed_5319_; lean_object* v_res_5320_; 
v_sz_boxed_5318_ = lean_unbox_usize(v_sz_5310_);
lean_dec(v_sz_5310_);
v_i_boxed_5319_ = lean_unbox_usize(v_i_5311_);
lean_dec(v_i_5311_);
v_res_5320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5318_, v_i_boxed_5319_, v_bs_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
lean_dec(v___y_5314_);
lean_dec_ref(v___y_5313_);
return v_res_5320_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5322_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5323_ = l_Lean_stringToMessageData(v___x_5322_);
return v___x_5323_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5325_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5326_ = l_Lean_stringToMessageData(v___x_5325_);
return v___x_5326_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; 
v___x_5328_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5329_ = l_Lean_stringToMessageData(v___x_5328_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5330_, lean_object* v_n_5331_, lean_object* v_xs_5332_, lean_object* v_x_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5363_; uint8_t v___x_5364_; 
v___x_5363_ = lean_array_get_size(v_xs_5332_);
v___x_5364_ = lean_nat_dec_eq(v___x_5363_, v_n_5331_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
lean_dec_ref(v_xs_5332_);
v___x_5365_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5366_ = l_Lean_MessageData_ofExpr(v_type_5330_);
v___x_5367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5365_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5367_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = l_Nat_reprFast(v_n_5331_);
v___x_5371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5370_);
v___x_5372_ = l_Lean_MessageData_ofFormat(v___x_5371_);
v___x_5373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5369_);
lean_ctor_set(v___x_5373_, 1, v___x_5372_);
v___x_5374_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5373_);
lean_ctor_set(v___x_5375_, 1, v___x_5374_);
v___x_5376_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5375_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
v_a_5377_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5376_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5376_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
else
{
lean_dec(v_n_5331_);
goto v___jp_5339_;
}
v___jp_5339_:
{
size_t v_sz_5340_; size_t v___x_5341_; lean_object* v___x_5342_; 
v_sz_5340_ = lean_array_size(v_xs_5332_);
v___x_5341_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5332_);
v___x_5342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5340_, v___x_5341_, v_xs_5332_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5344_; size_t v_sz_5345_; lean_object* v___x_5346_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5343_);
lean_dec_ref_known(v___x_5342_, 1);
v___x_5344_ = lean_box(0);
v_sz_5345_ = lean_array_size(v_a_5343_);
v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5332_, v_type_5330_, v_a_5343_, v_sz_5345_, v___x_5341_, v___x_5344_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec_ref(v_xs_5332_);
if (lean_obj_tag(v___x_5346_) == 0)
{
lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v___x_5346_, 0);
lean_dec(v_unused_5354_);
v___x_5348_ = v___x_5346_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_dec(v___x_5346_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
lean_ctor_set(v___x_5348_, 0, v_a_5343_);
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5343_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
lean_dec(v_a_5343_);
v_a_5355_ = lean_ctor_get(v___x_5346_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5346_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5346_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5332_);
lean_dec_ref(v_type_5330_);
return v___x_5342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5385_, lean_object* v_n_5386_, lean_object* v_xs_5387_, lean_object* v_x_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5385_, v_n_5386_, v_xs_5387_, v_x_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec_ref(v_x_5388_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5395_, lean_object* v_type_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v___f_5402_; lean_object* v___x_5403_; uint8_t v___x_5404_; lean_object* v___x_5405_; 
lean_inc(v_n_5395_);
lean_inc_ref(v_type_5396_);
v___f_5402_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5402_, 0, v_type_5396_);
lean_closure_set(v___f_5402_, 1, v_n_5395_);
v___x_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5403_, 0, v_n_5395_);
v___x_5404_ = 0;
v___x_5405_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5396_, v___x_5403_, v___f_5402_, v___x_5404_, v___x_5404_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5406_, lean_object* v_type_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l_Lean_Meta_arrowDomainsN(v_n_5406_, v_type_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_);
lean_dec(v_a_5411_);
lean_dec_ref(v_a_5410_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5414_, lean_object* v_e_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v___x_5421_; 
lean_inc(v_a_5419_);
lean_inc_ref(v_a_5418_);
lean_inc(v_a_5417_);
lean_inc_ref(v_a_5416_);
v___x_5421_ = lean_infer_type(v_e_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5423_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5422_);
lean_dec_ref_known(v___x_5421_, 1);
v___x_5423_ = l_Lean_Meta_arrowDomainsN(v_n_5414_, v_a_5422_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
return v___x_5423_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec(v_n_5414_);
v_a_5424_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5421_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5421_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5432_, lean_object* v_e_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Lean_Meta_inferArgumentTypesN(v_n_5432_, v_e_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
return v_res_5439_;
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
