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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
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
uint8_t l_Bool_toLBool(uint8_t);
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
lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_4858__overap_208_; lean_object* v___x_209_; 
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
v___x_4858__overap_208_ = lean_panic_fn_borrowed(v___x_207_, v_msg_187_);
lean_dec(v___x_207_);
v___x_209_ = lean_apply_1(v___x_4858__overap_208_, v___y_188_);
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
v___x_259_ = lean_unsigned_to_nat(94u);
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
v___x_265_ = lean_unsigned_to_nat(95u);
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
v___x_271_ = lean_unsigned_to_nat(96u);
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
v___x_277_ = lean_unsigned_to_nat(93u);
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
lean_dec_ref(v_fn_289_);
lean_dec_ref_known(v_e_284_, 2);
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
v___x_313_ = lean_unsigned_to_nat(1849u);
v___x_314_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_316_ = l_mkPanicMessageWithDecl(v___x_315_, v___x_314_, v___x_313_, v___x_312_, v___x_311_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_317_, lean_object* v_stop_318_, lean_object* v_args_319_, lean_object* v_e_320_, lean_object* v_f_321_, lean_object* v_a_322_, lean_object* v_offset_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_360_; 
lean_inc(v_offset_323_);
v___x_325_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_317_, v_stop_318_, v_args_319_, v_f_321_, v_offset_323_, v_a_324_);
v_fst_326_ = lean_ctor_get(v___x_325_, 0);
v_snd_327_ = lean_ctor_get(v___x_325_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_360_ == 0)
{
v___x_329_ = v___x_325_;
v_isShared_330_ = v_isSharedCheck_360_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_inc(v_fst_326_);
lean_dec(v___x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_360_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_359_; 
v___x_331_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_317_, v_stop_318_, v_args_319_, v_a_322_, v_offset_323_, v_snd_327_);
v_fst_332_ = lean_ctor_get(v___x_331_, 0);
v_snd_333_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_359_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_359_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snd_333_);
lean_inc(v_fst_332_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_359_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
uint8_t v___y_338_; 
if (lean_obj_tag(v_e_320_) == 5)
{
lean_object* v_fn_346_; lean_object* v_arg_347_; size_t v___x_348_; size_t v___x_349_; uint8_t v___x_350_; 
lean_del_object(v___x_329_);
v_fn_346_ = lean_ctor_get(v_e_320_, 0);
v_arg_347_ = lean_ctor_get(v_e_320_, 1);
v___x_348_ = lean_ptr_addr(v_fn_346_);
v___x_349_ = lean_ptr_addr(v_fst_326_);
v___x_350_ = lean_usize_dec_eq(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
v___y_338_ = v___x_350_;
goto v___jp_337_;
}
else
{
size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_ptr_addr(v_arg_347_);
v___x_352_ = lean_ptr_addr(v_fst_332_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
v___y_338_ = v___x_353_;
goto v___jp_337_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
lean_del_object(v___x_335_);
lean_dec(v_fst_332_);
lean_dec(v_fst_326_);
lean_dec_ref(v_e_320_);
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_355_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_354_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_snd_333_);
lean_ctor_set(v___x_329_, 0, v___x_355_);
v___x_357_ = v___x_329_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_snd_333_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
v___jp_337_:
{
if (v___y_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec_ref(v_e_320_);
v___x_339_ = l_Lean_Expr_app___override(v_fst_326_, v_fst_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_339_);
v___x_341_ = v___x_335_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_snd_333_);
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
lean_object* v___x_344_; 
lean_dec(v_fst_332_);
lean_dec(v_fst_326_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v_e_320_);
v___x_344_ = v___x_335_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_e_320_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_333_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_362_ = lean_unsigned_to_nat(21u);
v___x_363_ = lean_unsigned_to_nat(97u);
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_366_ = l_mkPanicMessageWithDecl(v___x_365_, v___x_364_, v___x_363_, v___x_362_, v___x_361_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_367_, lean_object* v_stop_368_, lean_object* v_args_369_, lean_object* v_e_370_, lean_object* v_offset_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = l_Lean_Expr_looseBVarRange(v_e_370_);
v___x_374_ = lean_nat_dec_le(v___x_373_, v_offset_371_);
lean_dec(v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v___y_382_; lean_object* v___x_385_; 
lean_inc(v_offset_371_);
lean_inc_ref(v_e_370_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_e_370_);
lean_ctor_set(v___x_375_, 1, v_offset_371_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_372_, v___x_375_);
if (lean_obj_tag(v___x_385_) == 0)
{
switch(lean_obj_tag(v_e_370_))
{
case 0:
{
lean_object* v_deBruijnIndex_386_; lean_object* v___x_387_; 
v_deBruijnIndex_386_ = lean_ctor_get(v_e_370_, 0);
lean_inc(v_deBruijnIndex_386_);
lean_dec_ref_known(v_e_370_, 1);
v___x_387_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_367_, v_stop_368_, v_args_369_, v_deBruijnIndex_386_, v_offset_371_);
lean_dec(v_offset_371_);
lean_dec(v_deBruijnIndex_386_);
v_fst_377_ = v___x_387_;
v_snd_378_ = v_a_372_;
goto v___jp_376_;
}
case 1:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref_known(v_e_370_, 1);
lean_dec(v_offset_371_);
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_389_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_388_, v_a_372_);
v___y_382_ = v___x_389_;
goto v___jp_381_;
}
case 2:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref_known(v_e_370_, 1);
lean_dec(v_offset_371_);
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_391_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_390_, v_a_372_);
v___y_382_ = v___x_391_;
goto v___jp_381_;
}
case 3:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref_known(v_e_370_, 1);
lean_dec(v_offset_371_);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_393_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_392_, v_a_372_);
v___y_382_ = v___x_393_;
goto v___jp_381_;
}
case 4:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref_known(v_e_370_, 2);
lean_dec(v_offset_371_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_395_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_394_, v_a_372_);
v___y_382_ = v___x_395_;
goto v___jp_381_;
}
case 5:
{
lean_object* v_fn_396_; lean_object* v_arg_397_; lean_object* v_head_398_; uint8_t v___x_399_; 
v_fn_396_ = lean_ctor_get(v_e_370_, 0);
v_arg_397_ = lean_ctor_get(v_e_370_, 1);
v_head_398_ = l_Lean_Expr_getAppFn(v_e_370_);
v___x_399_ = l_Lean_Expr_isBVar(v_head_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_inc_ref(v_arg_397_);
lean_inc_ref(v_fn_396_);
lean_dec_ref(v_head_398_);
v___x_400_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_367_, v_stop_368_, v_args_369_, v_e_370_, v_fn_396_, v_arg_397_, v_offset_371_, v_a_372_);
v___y_382_ = v___x_400_;
goto v___jp_381_;
}
else
{
lean_object* v___x_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; size_t v_sz_407_; size_t v___x_408_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_412_; 
lean_inc(v_offset_371_);
v___x_401_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_head_398_, v_offset_371_, v_a_372_);
v_fst_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_fst_402_);
v_snd_403_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_snd_403_);
lean_dec_ref(v___x_401_);
v___x_404_ = l_Lean_Expr_getAppNumArgs(v_e_370_);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
lean_dec(v___x_404_);
v___x_406_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_370_, v___x_405_);
v_sz_407_ = lean_array_size(v___x_406_);
v___x_408_ = ((size_t)0ULL);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_367_, v_stop_368_, v_args_369_, v_offset_371_, v_sz_407_, v___x_408_, v___x_406_, v_snd_403_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
v___x_412_ = l_Lean_Expr_betaRev(v_fst_402_, v_fst_410_, v___x_374_, v___x_374_);
lean_dec(v_fst_410_);
v_fst_377_ = v___x_412_;
v_snd_378_ = v_snd_411_;
goto v___jp_376_;
}
}
case 6:
{
lean_object* v_binderName_413_; lean_object* v_binderType_414_; lean_object* v_body_415_; uint8_t v_binderInfo_416_; lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; uint8_t v___y_426_; size_t v___x_430_; size_t v___x_431_; uint8_t v___x_432_; 
v_binderName_413_ = lean_ctor_get(v_e_370_, 0);
v_binderType_414_ = lean_ctor_get(v_e_370_, 1);
v_body_415_ = lean_ctor_get(v_e_370_, 2);
v_binderInfo_416_ = lean_ctor_get_uint8(v_e_370_, sizeof(void*)*3 + 8);
lean_inc(v_offset_371_);
lean_inc_ref(v_binderType_414_);
v___x_417_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_binderType_414_, v_offset_371_, v_a_372_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_fst_418_);
v_snd_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_snd_419_);
lean_dec_ref(v___x_417_);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_add(v_offset_371_, v___x_420_);
lean_dec(v_offset_371_);
lean_inc_ref(v_body_415_);
v___x_422_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_body_415_, v___x_421_, v_snd_419_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___x_422_);
v___x_430_ = lean_ptr_addr(v_binderType_414_);
v___x_431_ = lean_ptr_addr(v_fst_418_);
v___x_432_ = lean_usize_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
v___y_426_ = v___x_432_;
goto v___jp_425_;
}
else
{
size_t v___x_433_; size_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_ptr_addr(v_body_415_);
v___x_434_ = lean_ptr_addr(v_fst_423_);
v___x_435_ = lean_usize_dec_eq(v___x_433_, v___x_434_);
v___y_426_ = v___x_435_;
goto v___jp_425_;
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_427_; 
lean_inc(v_binderName_413_);
lean_dec_ref_known(v_e_370_, 3);
v___x_427_ = l_Lean_Expr_lam___override(v_binderName_413_, v_fst_418_, v_fst_423_, v_binderInfo_416_);
v_fst_377_ = v___x_427_;
v_snd_378_ = v_snd_424_;
goto v___jp_376_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_416_, v_binderInfo_416_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_inc(v_binderName_413_);
lean_dec_ref_known(v_e_370_, 3);
v___x_429_ = l_Lean_Expr_lam___override(v_binderName_413_, v_fst_418_, v_fst_423_, v_binderInfo_416_);
v_fst_377_ = v___x_429_;
v_snd_378_ = v_snd_424_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_423_);
lean_dec(v_fst_418_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_424_;
goto v___jp_376_;
}
}
}
}
case 7:
{
lean_object* v_binderName_436_; lean_object* v_binderType_437_; lean_object* v_body_438_; uint8_t v_binderInfo_439_; lean_object* v___x_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; uint8_t v___y_449_; size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v_binderName_436_ = lean_ctor_get(v_e_370_, 0);
v_binderType_437_ = lean_ctor_get(v_e_370_, 1);
v_body_438_ = lean_ctor_get(v_e_370_, 2);
v_binderInfo_439_ = lean_ctor_get_uint8(v_e_370_, sizeof(void*)*3 + 8);
lean_inc(v_offset_371_);
lean_inc_ref(v_binderType_437_);
v___x_440_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_binderType_437_, v_offset_371_, v_a_372_);
v_fst_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_snd_442_);
lean_dec_ref(v___x_440_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_offset_371_, v___x_443_);
lean_dec(v_offset_371_);
lean_inc_ref(v_body_438_);
v___x_445_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_body_438_, v___x_444_, v_snd_442_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_445_);
v___x_453_ = lean_ptr_addr(v_binderType_437_);
v___x_454_ = lean_ptr_addr(v_fst_441_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
v___y_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_ptr_addr(v_body_438_);
v___x_457_ = lean_ptr_addr(v_fst_446_);
v___x_458_ = lean_usize_dec_eq(v___x_456_, v___x_457_);
v___y_449_ = v___x_458_;
goto v___jp_448_;
}
v___jp_448_:
{
if (v___y_449_ == 0)
{
lean_object* v___x_450_; 
lean_inc(v_binderName_436_);
lean_dec_ref_known(v_e_370_, 3);
v___x_450_ = l_Lean_Expr_forallE___override(v_binderName_436_, v_fst_441_, v_fst_446_, v_binderInfo_439_);
v_fst_377_ = v___x_450_;
v_snd_378_ = v_snd_447_;
goto v___jp_376_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_439_, v_binderInfo_439_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_inc(v_binderName_436_);
lean_dec_ref_known(v_e_370_, 3);
v___x_452_ = l_Lean_Expr_forallE___override(v_binderName_436_, v_fst_441_, v_fst_446_, v_binderInfo_439_);
v_fst_377_ = v___x_452_;
v_snd_378_ = v_snd_447_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_446_);
lean_dec(v_fst_441_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_447_;
goto v___jp_376_;
}
}
}
}
case 8:
{
lean_object* v_declName_459_; lean_object* v_type_460_; lean_object* v_value_461_; lean_object* v_body_462_; uint8_t v_nondep_463_; lean_object* v___x_464_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; uint8_t v___y_476_; size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v_declName_459_ = lean_ctor_get(v_e_370_, 0);
v_type_460_ = lean_ctor_get(v_e_370_, 1);
v_value_461_ = lean_ctor_get(v_e_370_, 2);
v_body_462_ = lean_ctor_get(v_e_370_, 3);
v_nondep_463_ = lean_ctor_get_uint8(v_e_370_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_371_, 2);
lean_inc_ref(v_type_460_);
v___x_464_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_type_460_, v_offset_371_, v_a_372_);
v_fst_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_fst_465_);
v_snd_466_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v___x_464_);
lean_inc_ref(v_value_461_);
v___x_467_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_value_461_, v_offset_371_, v_snd_466_);
v_fst_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_fst_468_);
v_snd_469_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_469_);
lean_dec_ref(v___x_467_);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_add(v_offset_371_, v___x_470_);
lean_dec(v_offset_371_);
lean_inc_ref(v_body_462_);
v___x_472_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_body_462_, v___x_471_, v_snd_469_);
v_fst_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v___x_472_, 1);
lean_inc(v_snd_474_);
lean_dec_ref(v___x_472_);
v___x_482_ = lean_ptr_addr(v_type_460_);
v___x_483_ = lean_ptr_addr(v_fst_465_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
v___y_476_ = v___x_484_;
goto v___jp_475_;
}
else
{
size_t v___x_485_; size_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_ptr_addr(v_value_461_);
v___x_486_ = lean_ptr_addr(v_fst_468_);
v___x_487_ = lean_usize_dec_eq(v___x_485_, v___x_486_);
v___y_476_ = v___x_487_;
goto v___jp_475_;
}
v___jp_475_:
{
if (v___y_476_ == 0)
{
lean_object* v___x_477_; 
lean_inc(v_declName_459_);
lean_dec_ref_known(v_e_370_, 4);
v___x_477_ = l_Lean_Expr_letE___override(v_declName_459_, v_fst_465_, v_fst_468_, v_fst_473_, v_nondep_463_);
v_fst_377_ = v___x_477_;
v_snd_378_ = v_snd_474_;
goto v___jp_376_;
}
else
{
size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_ptr_addr(v_body_462_);
v___x_479_ = lean_ptr_addr(v_fst_473_);
v___x_480_ = lean_usize_dec_eq(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_inc(v_declName_459_);
lean_dec_ref_known(v_e_370_, 4);
v___x_481_ = l_Lean_Expr_letE___override(v_declName_459_, v_fst_465_, v_fst_468_, v_fst_473_, v_nondep_463_);
v_fst_377_ = v___x_481_;
v_snd_378_ = v_snd_474_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_473_);
lean_dec(v_fst_468_);
lean_dec(v_fst_465_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_474_;
goto v___jp_376_;
}
}
}
}
case 9:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref_known(v_e_370_, 1);
lean_dec(v_offset_371_);
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_489_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_488_, v_a_372_);
v___y_382_ = v___x_489_;
goto v___jp_381_;
}
case 10:
{
lean_object* v_data_490_; lean_object* v_expr_491_; lean_object* v___x_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v_data_490_ = lean_ctor_get(v_e_370_, 0);
v_expr_491_ = lean_ctor_get(v_e_370_, 1);
lean_inc_ref(v_expr_491_);
v___x_492_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_expr_491_, v_offset_371_, v_a_372_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v___x_492_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_492_);
v___x_495_ = lean_ptr_addr(v_expr_491_);
v___x_496_ = lean_ptr_addr(v_fst_493_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_inc(v_data_490_);
lean_dec_ref_known(v_e_370_, 2);
v___x_498_ = l_Lean_Expr_mdata___override(v_data_490_, v_fst_493_);
v_fst_377_ = v___x_498_;
v_snd_378_ = v_snd_494_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_493_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_494_;
goto v___jp_376_;
}
}
default: 
{
lean_object* v_typeName_499_; lean_object* v_idx_500_; lean_object* v_struct_501_; lean_object* v___x_502_; lean_object* v_fst_503_; lean_object* v_snd_504_; size_t v___x_505_; size_t v___x_506_; uint8_t v___x_507_; 
v_typeName_499_ = lean_ctor_get(v_e_370_, 0);
v_idx_500_ = lean_ctor_get(v_e_370_, 1);
v_struct_501_ = lean_ctor_get(v_e_370_, 2);
lean_inc_ref(v_struct_501_);
v___x_502_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_struct_501_, v_offset_371_, v_a_372_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_fst_503_);
v_snd_504_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_snd_504_);
lean_dec_ref(v___x_502_);
v___x_505_ = lean_ptr_addr(v_struct_501_);
v___x_506_ = lean_ptr_addr(v_fst_503_);
v___x_507_ = lean_usize_dec_eq(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_inc(v_idx_500_);
lean_inc(v_typeName_499_);
lean_dec_ref_known(v_e_370_, 3);
v___x_508_ = l_Lean_Expr_proj___override(v_typeName_499_, v_idx_500_, v_fst_503_);
v_fst_377_ = v___x_508_;
v_snd_378_ = v_snd_504_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_503_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_504_;
goto v___jp_376_;
}
}
}
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; 
lean_dec_ref_known(v___x_375_, 2);
lean_dec(v_offset_371_);
lean_dec_ref(v_e_370_);
v_val_509_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v___x_385_, 1);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_val_509_);
lean_ctor_set(v___x_510_, 1, v_a_372_);
return v___x_510_;
}
v___jp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc_ref(v_fst_377_);
v___x_379_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_378_, v___x_375_, v_fst_377_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_fst_377_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
return v___x_380_;
}
v___jp_381_:
{
lean_object* v_fst_383_; lean_object* v_snd_384_; 
v_fst_383_ = lean_ctor_get(v___y_382_, 0);
lean_inc(v_fst_383_);
v_snd_384_ = lean_ctor_get(v___y_382_, 1);
lean_inc(v_snd_384_);
lean_dec_ref(v___y_382_);
v_fst_377_ = v_fst_383_;
v_snd_378_ = v_snd_384_;
goto v___jp_376_;
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_offset_371_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_e_370_);
lean_ctor_set(v___x_511_, 1, v_a_372_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_512_, lean_object* v_stop_513_, lean_object* v_args_514_, lean_object* v_offset_515_, size_t v_sz_516_, size_t v_i_517_, lean_object* v_bs_518_, lean_object* v___y_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_lt(v_i_517_, v_sz_516_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_offset_515_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_bs_518_);
lean_ctor_set(v___x_521_, 1, v___y_519_);
return v___x_521_;
}
else
{
lean_object* v_v_522_; lean_object* v___x_523_; lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_526_; lean_object* v_bs_x27_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v_v_522_ = lean_array_uget_borrowed(v_bs_518_, v_i_517_);
lean_inc(v_offset_515_);
lean_inc(v_v_522_);
v___x_523_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_512_, v_stop_513_, v_args_514_, v_v_522_, v_offset_515_, v___y_519_);
v_fst_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_fst_524_);
v_snd_525_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_snd_525_);
lean_dec_ref(v___x_523_);
v___x_526_ = lean_unsigned_to_nat(0u);
v_bs_x27_527_ = lean_array_uset(v_bs_518_, v_i_517_, v___x_526_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_517_, v___x_528_);
v___x_530_ = lean_array_uset(v_bs_x27_527_, v_i_517_, v_fst_524_);
v_i_517_ = v___x_529_;
v_bs_518_ = v___x_530_;
v___y_519_ = v_snd_525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_532_, lean_object* v_stop_533_, lean_object* v_args_534_, lean_object* v_offset_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_, lean_object* v___y_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_541_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_532_, v_stop_533_, v_args_534_, v_offset_535_, v_sz_boxed_540_, v_i_boxed_541_, v_bs_538_, v___y_539_);
lean_dec_ref(v_args_534_);
lean_dec(v_stop_533_);
lean_dec(v_start_532_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_543_, lean_object* v_stop_544_, lean_object* v_args_545_, lean_object* v_e_546_, lean_object* v_offset_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_543_, v_stop_544_, v_args_545_, v_e_546_, v_offset_547_, v_a_548_);
lean_dec_ref(v_args_545_);
lean_dec(v_stop_544_);
lean_dec(v_start_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_550_, lean_object* v_stop_551_, lean_object* v_args_552_, lean_object* v_e_553_, lean_object* v_f_554_, lean_object* v_a_555_, lean_object* v_offset_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_550_, v_stop_551_, v_args_552_, v_e_553_, v_f_554_, v_a_555_, v_offset_556_, v_a_557_);
lean_dec_ref(v_args_552_);
lean_dec(v_stop_551_);
lean_dec(v_start_550_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_559_, lean_object* v_stop_560_, lean_object* v_args_561_, lean_object* v_e_562_, lean_object* v_offset_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_559_, v_stop_560_, v_args_561_, v_e_562_, v_offset_563_, v_a_564_);
lean_dec_ref(v_args_561_);
lean_dec(v_stop_560_);
lean_dec(v_start_559_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_566_, lean_object* v_m_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_567_, v_a_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_570_, v_m_571_, v_a_572_);
lean_dec_ref(v_a_572_);
lean_dec_ref(v_m_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_, lean_object* v_b_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_575_, v_a_576_, v_b_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_579_, lean_object* v_a_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_583_, lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_583_, v_a_584_, v_x_585_);
lean_dec(v_x_585_);
lean_dec_ref(v_a_584_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_587_, lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_591_, lean_object* v_a_592_, lean_object* v_x_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_591_, v_a_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_a_592_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object* v_00_u03b2_596_, lean_object* v_data_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_data_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object* v_00_u03b2_599_, lean_object* v_a_600_, lean_object* v_b_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_600_, v_b_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_604_, lean_object* v_i_605_, lean_object* v_source_606_, lean_object* v_target_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v_i_605_, v_source_606_, v_target_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
v___x_618_ = l_Lean_Expr_consumeMData(v___x_617_);
v___x_619_ = l_Lean_Expr_isLambda(v___x_618_);
lean_dec_ref(v___x_618_);
if (v___x_619_ == 0)
{
size_t v___x_620_; size_t v___x_621_; 
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_614_, v___x_620_);
v_i_614_ = v___x_621_;
goto _start;
}
else
{
return v___x_619_;
}
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_624_, lean_object* v_i_625_, lean_object* v_stop_626_){
_start:
{
size_t v_i_boxed_627_; size_t v_stop_boxed_628_; uint8_t v_res_629_; lean_object* v_r_630_; 
v_i_boxed_627_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_stop_boxed_628_ = lean_unbox_usize(v_stop_626_);
lean_dec(v_stop_626_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_624_, v_i_boxed_627_, v_stop_boxed_628_);
lean_dec_ref(v_as_624_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = lean_unsigned_to_nat(16u);
v___x_633_ = lean_mk_array(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__0, &l_Lean_Expr_instantiateBetaRevRange___closed__0_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__0);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__3));
v___x_640_ = lean_unsigned_to_nat(4u);
v___x_641_ = lean_unsigned_to_nat(37u);
v___x_642_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__2));
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_644_ = l_mkPanicMessageWithDecl(v___x_643_, v___x_642_, v___x_641_, v___x_640_, v___x_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_645_, lean_object* v_start_646_, lean_object* v_stop_647_, lean_object* v_args_648_){
_start:
{
lean_object* v___y_650_; uint8_t v___y_662_; uint8_t v___x_669_; 
v___x_669_ = l_Lean_Expr_hasLooseBVars(v_e_645_);
if (v___x_669_ == 0)
{
v___y_662_ = v___x_669_;
goto v___jp_661_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v_start_646_, v_stop_647_);
v___y_662_ = v___x_670_;
goto v___jp_661_;
}
v___jp_649_:
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_lt(v_start_646_, v___y_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v___y_650_);
v___x_652_ = lean_expr_instantiate_rev_range(v_e_645_, v_start_646_, v_stop_647_, v_args_648_);
lean_dec(v_stop_647_);
lean_dec_ref(v_e_645_);
return v___x_652_;
}
else
{
size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_usize_of_nat(v_start_646_);
v___x_654_ = lean_usize_of_nat(v___y_650_);
lean_dec(v___y_650_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_648_, v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_expr_instantiate_rev_range(v_e_645_, v_start_646_, v_stop_647_, v_args_648_);
lean_dec(v_stop_647_);
lean_dec_ref(v_e_645_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_fst_660_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__1, &l_Lean_Expr_instantiateBetaRevRange___closed__1_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__1);
v___x_659_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_646_, v_stop_647_, v_args_648_, v_e_645_, v___x_657_, v___x_658_);
lean_dec(v_stop_647_);
v_fst_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_fst_660_);
lean_dec_ref(v___x_659_);
return v_fst_660_;
}
}
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_dec(v_stop_647_);
return v_e_645_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_array_get_size(v_args_648_);
v___x_664_ = lean_nat_dec_le(v_stop_647_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_stop_647_);
lean_dec_ref(v_e_645_);
v___x_665_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_666_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_665_);
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_lt(v_start_646_, v_stop_647_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_expr_instantiate_rev_range(v_e_645_, v_start_646_, v_stop_647_, v_args_648_);
lean_dec(v_stop_647_);
lean_dec_ref(v_e_645_);
return v___x_668_;
}
else
{
if (v___x_664_ == 0)
{
v___y_650_ = v___x_663_;
goto v___jp_649_;
}
else
{
lean_inc(v_stop_647_);
v___y_650_ = v_stop_647_;
goto v___jp_649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_671_, lean_object* v_start_672_, lean_object* v_stop_673_, lean_object* v_args_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Expr_instantiateBetaRevRange(v_e_671_, v_start_672_, v_stop_673_, v_args_674_);
lean_dec_ref(v_args_674_);
lean_dec(v_start_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; lean_object* v_env_683_; lean_object* v___x_684_; lean_object* v_mctx_685_; lean_object* v_lctx_686_; lean_object* v_options_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_682_ = lean_st_ref_get(v___y_680_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_env_683_);
lean_dec(v___x_682_);
v___x_684_ = lean_st_ref_get(v___y_678_);
v_mctx_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_mctx_685_);
lean_dec(v___x_684_);
v_lctx_686_ = lean_ctor_get(v___y_677_, 2);
v_options_687_ = lean_ctor_get(v___y_679_, 2);
lean_inc_ref(v_options_687_);
lean_inc_ref(v_lctx_686_);
v___x_688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_688_, 0, v_env_683_);
lean_ctor_set(v___x_688_, 1, v_mctx_685_);
lean_ctor_set(v___x_688_, 2, v_lctx_686_);
lean_ctor_set(v___x_688_, 3, v_options_687_);
v___x_689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_msgData_676_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_ref_704_; lean_object* v___x_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_ref_704_ = lean_ctor_get(v___y_701_, 5);
v___x_705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_inc(v_ref_704_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_ref_704_);
lean_ctor_set(v___x_710_, 1, v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_732_ = l_Lean_indentExpr(v_f_725_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_733_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_742_, lean_object* v_f_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_750_, lean_object* v_f_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_750_, v_f_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_758_, lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_766_, lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_766_, v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_774_, lean_object* v_args_775_, lean_object* v_f_776_, lean_object* v_a_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_a_785_; uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_lt(v_a_777_, v_upperBound_774_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v_a_777_);
lean_dec_ref(v_f_776_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_b_778_);
return v___x_790_;
}
else
{
lean_object* v_fst_791_; 
v_fst_791_ = lean_ctor_get(v_b_778_, 0);
lean_inc(v_fst_791_);
if (lean_obj_tag(v_fst_791_) == 7)
{
lean_object* v_snd_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_snd_792_ = lean_ctor_get(v_b_778_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_b_778_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_b_778_, 0);
lean_dec(v_unused_801_);
v___x_794_ = v_b_778_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_792_);
lean_dec(v_b_778_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_body_796_; lean_object* v___x_798_; 
v_body_796_ = lean_ctor_get(v_fst_791_, 2);
lean_inc_ref(v_body_796_);
lean_dec_ref_known(v_fst_791_, 3);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_body_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_body_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_792_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_a_785_ = v___x_798_;
goto v___jp_784_;
}
}
}
else
{
lean_object* v_snd_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_837_; 
v_snd_802_ = lean_ctor_get(v_b_778_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_b_778_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v_b_778_, 0);
lean_dec(v_unused_838_);
v___x_804_ = v_b_778_;
v_isShared_805_ = v_isSharedCheck_837_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_snd_802_);
lean_dec(v_b_778_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_837_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_inc(v_a_777_);
lean_inc(v_fst_791_);
v___x_806_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_791_, v_snd_802_, v_a_777_, v_args_775_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc_ref(v___y_779_);
v___x_807_ = lean_whnf(v___x_806_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
if (lean_obj_tag(v_a_808_) == 7)
{
lean_object* v_body_809_; lean_object* v___x_811_; 
lean_dec(v_snd_802_);
lean_dec(v_fst_791_);
v_body_809_ = lean_ctor_get(v_a_808_, 2);
lean_inc_ref(v_body_809_);
lean_dec_ref_known(v_a_808_, 3);
lean_inc(v_a_777_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v_a_777_);
lean_ctor_set(v___x_804_, 0, v_body_809_);
v___x_811_ = v___x_804_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_body_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_777_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v_a_785_ = v___x_811_;
goto v___jp_784_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec(v_a_808_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_a_777_, v___x_814_);
lean_inc_ref(v_f_776_);
v___x_816_ = l_Lean_mkAppRange(v_f_776_, v___x_813_, v___x_815_, v_args_775_);
lean_dec(v___x_815_);
v___x_817_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_816_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_819_; 
lean_dec_ref_known(v___x_817_, 1);
if (v_isShared_805_ == 0)
{
v___x_819_ = v___x_804_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_791_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_snd_802_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_a_785_ = v___x_819_;
goto v___jp_784_;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_del_object(v___x_804_);
lean_dec(v_snd_802_);
lean_dec(v_fst_791_);
lean_dec(v_a_777_);
lean_dec_ref(v_f_776_);
v_a_821_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_817_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_817_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_del_object(v___x_804_);
lean_dec(v_snd_802_);
lean_dec(v_fst_791_);
lean_dec(v_a_777_);
lean_dec_ref(v_f_776_);
v_a_829_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_807_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_807_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_a_777_, v___x_786_);
lean_dec(v_a_777_);
v_a_777_ = v___x_787_;
v_b_778_ = v_a_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_839_, lean_object* v_args_840_, lean_object* v_f_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_839_, v_args_840_, v_f_841_, v_a_842_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_args_840_);
lean_dec(v_upperBound_839_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_850_, lean_object* v_args_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
lean_inc(v_a_855_);
lean_inc_ref(v_a_854_);
lean_inc(v_a_853_);
lean_inc_ref(v_a_852_);
lean_inc_ref(v_f_850_);
v___x_857_ = lean_infer_type(v_f_850_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_array_get_size(v_args_851_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_a_858_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_859_, v_args_851_, v_f_850_, v___x_860_, v___x_861_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_873_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_873_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_873_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v_fst_867_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v_a_863_, 1);
lean_inc(v_snd_868_);
lean_dec(v_a_863_);
v___x_869_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_867_, v_snd_868_, v___x_859_, v_args_851_);
lean_dec(v_snd_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_862_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_862_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_dec_ref(v_f_850_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_882_, lean_object* v_args_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_882_, v_args_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec_ref(v_args_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_890_, lean_object* v_args_891_, lean_object* v_f_892_, lean_object* v_inst_893_, lean_object* v_R_894_, lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v_c_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_890_, v_args_891_, v_f_892_, v_a_895_, v_b_896_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_904_, lean_object* v_args_905_, lean_object* v_f_906_, lean_object* v_inst_907_, lean_object* v_R_908_, lean_object* v_a_909_, lean_object* v_b_910_, lean_object* v_c_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_904_, v_args_905_, v_f_906_, v_inst_907_, v_R_908_, v_a_909_, v_b_910_, v_c_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_args_905_);
lean_dec(v_upperBound_904_);
return v_res_917_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_921_, lean_object* v_us_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_928_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_929_ = l_Lean_mkConst(v_constName_921_, v_us_922_);
v___x_930_ = l_Lean_MessageData_ofExpr(v___x_929_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_928_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_931_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_933_, lean_object* v_us_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_933_, v_us_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_941_, lean_object* v_constName_942_, lean_object* v_us_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_942_, v_us_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_950_, lean_object* v_constName_951_, lean_object* v_us_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_950_, v_constName_951_, v_us_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_fileName_966_; lean_object* v_fileMap_967_; lean_object* v_options_968_; lean_object* v_currRecDepth_969_; lean_object* v_maxRecDepth_970_; lean_object* v_ref_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v_initHeartbeats_974_; lean_object* v_maxHeartbeats_975_; lean_object* v_quotContext_976_; lean_object* v_currMacroScope_977_; uint8_t v_diag_978_; lean_object* v_cancelTk_x3f_979_; uint8_t v_suppressElabErrors_980_; lean_object* v_inheritedTraceOptions_981_; lean_object* v_ref_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_fileName_966_ = lean_ctor_get(v___y_963_, 0);
v_fileMap_967_ = lean_ctor_get(v___y_963_, 1);
v_options_968_ = lean_ctor_get(v___y_963_, 2);
v_currRecDepth_969_ = lean_ctor_get(v___y_963_, 3);
v_maxRecDepth_970_ = lean_ctor_get(v___y_963_, 4);
v_ref_971_ = lean_ctor_get(v___y_963_, 5);
v_currNamespace_972_ = lean_ctor_get(v___y_963_, 6);
v_openDecls_973_ = lean_ctor_get(v___y_963_, 7);
v_initHeartbeats_974_ = lean_ctor_get(v___y_963_, 8);
v_maxHeartbeats_975_ = lean_ctor_get(v___y_963_, 9);
v_quotContext_976_ = lean_ctor_get(v___y_963_, 10);
v_currMacroScope_977_ = lean_ctor_get(v___y_963_, 11);
v_diag_978_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14);
v_cancelTk_x3f_979_ = lean_ctor_get(v___y_963_, 12);
v_suppressElabErrors_980_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_981_ = lean_ctor_get(v___y_963_, 13);
v_ref_982_ = l_Lean_replaceRef(v_ref_959_, v_ref_971_);
lean_inc_ref(v_inheritedTraceOptions_981_);
lean_inc(v_cancelTk_x3f_979_);
lean_inc(v_currMacroScope_977_);
lean_inc(v_quotContext_976_);
lean_inc(v_maxHeartbeats_975_);
lean_inc(v_initHeartbeats_974_);
lean_inc(v_openDecls_973_);
lean_inc(v_currNamespace_972_);
lean_inc(v_maxRecDepth_970_);
lean_inc(v_currRecDepth_969_);
lean_inc_ref(v_options_968_);
lean_inc_ref(v_fileMap_967_);
lean_inc_ref(v_fileName_966_);
v___x_983_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_983_, 0, v_fileName_966_);
lean_ctor_set(v___x_983_, 1, v_fileMap_967_);
lean_ctor_set(v___x_983_, 2, v_options_968_);
lean_ctor_set(v___x_983_, 3, v_currRecDepth_969_);
lean_ctor_set(v___x_983_, 4, v_maxRecDepth_970_);
lean_ctor_set(v___x_983_, 5, v_ref_982_);
lean_ctor_set(v___x_983_, 6, v_currNamespace_972_);
lean_ctor_set(v___x_983_, 7, v_openDecls_973_);
lean_ctor_set(v___x_983_, 8, v_initHeartbeats_974_);
lean_ctor_set(v___x_983_, 9, v_maxHeartbeats_975_);
lean_ctor_set(v___x_983_, 10, v_quotContext_976_);
lean_ctor_set(v___x_983_, 11, v_currMacroScope_977_);
lean_ctor_set(v___x_983_, 12, v_cancelTk_x3f_979_);
lean_ctor_set(v___x_983_, 13, v_inheritedTraceOptions_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14, v_diag_978_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*14 + 1, v_suppressElabErrors_980_);
v___x_984_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_960_, v___y_961_, v___y_962_, v___x_983_, v___y_964_);
lean_dec_ref_known(v___x_983_, 14);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_985_, v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_ref_985_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
lean_ctor_set(v___x_998_, 3, v___x_997_);
lean_ctor_set(v___x_998_, 4, v___x_996_);
lean_ctor_set(v___x_998_, 5, v___x_996_);
lean_ctor_set(v___x_998_, 6, v___x_996_);
lean_ctor_set(v___x_998_, 7, v___x_996_);
lean_ctor_set(v___x_998_, 8, v___x_996_);
lean_ctor_set(v___x_998_, 9, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(32u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1002_ = ((size_t)5ULL);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_unsigned_to_nat(32u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1007_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1003_);
lean_ctor_set(v___x_1007_, 3, v___x_1003_);
lean_ctor_set_usize(v___x_1007_, 4, v___x_1002_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = lean_box(1);
v___x_1009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1033_, lean_object* v_declHint_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_env_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_st_ref_get(v___y_1035_);
v_env_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc_ref(v_env_1038_);
lean_dec(v___x_1037_);
v___x_1039_ = l_Lean_Name_isAnonymous(v_declHint_1034_);
if (v___x_1039_ == 0)
{
uint8_t v_isExporting_1040_; 
v_isExporting_1040_ = lean_ctor_get_uint8(v_env_1038_, sizeof(void*)*8);
if (v_isExporting_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_msg_1033_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc_ref(v_env_1038_);
v___x_1042_ = l_Lean_Environment_setExporting(v_env_1038_, v___x_1039_);
lean_inc(v_declHint_1034_);
lean_inc_ref(v___x_1042_);
v___x_1043_ = l_Lean_Environment_contains(v___x_1042_, v_declHint_1034_, v_isExporting_1040_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v_msg_1033_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_c_1050_; lean_object* v___x_1051_; 
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1047_ = l_Lean_Options_empty;
v___x_1048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1042_);
lean_ctor_set(v___x_1048_, 1, v___x_1045_);
lean_ctor_set(v___x_1048_, 2, v___x_1046_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
lean_inc(v_declHint_1034_);
v___x_1049_ = l_Lean_MessageData_ofConstName(v_declHint_1034_, v___x_1039_);
v_c_1050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1050_, 0, v___x_1048_);
lean_ctor_set(v_c_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1038_, v_declHint_1034_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_c_1050_);
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_note(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_msg_1033_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1094_; 
v_val_1059_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1061_ = v___x_1051_;
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1051_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_mod_1066_; uint8_t v___x_1067_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_Environment_header(v_env_1038_);
lean_dec_ref(v_env_1038_);
v___x_1065_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1064_);
v_mod_1066_ = lean_array_get(v___x_1063_, v___x_1065_, v_val_1059_);
lean_dec(v_val_1059_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_isPrivateName(v_declHint_1034_);
lean_dec(v_declHint_1034_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_c_1050_);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_MessageData_ofName(v_mod_1066_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_MessageData_note(v___x_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_msg_1033_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1077_);
v___x_1079_ = v___x_1061_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_c_1050_);
v___x_1083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_MessageData_ofName(v_mod_1066_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_MessageData_note(v___x_1088_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_msg_1033_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1090_);
v___x_1092_ = v___x_1061_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1095_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_msg_1033_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1096_, v_declHint_1097_, v___y_1098_);
lean_dec(v___y_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1118_; 
v___x_1108_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1101_, v_declHint_1102_, v___y_1106_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1113_ = l_Lean_unknownIdentifierMessageTag;
v___x_1114_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1119_, lean_object* v_declHint_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1119_, v_declHint_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1127_, lean_object* v_msg_1128_, lean_object* v_declHint_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v_a_1136_; lean_object* v___x_1137_; 
v___x_1135_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1128_, v_declHint_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1127_, v_a_1136_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1138_, lean_object* v_msg_1139_, lean_object* v_declHint_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1138_, v_msg_1139_, v_declHint_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v_ref_1138_);
return v_res_1146_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1153_, lean_object* v_constName_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1160_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1161_ = 0;
lean_inc(v_constName_1154_);
v___x_1162_ = l_Lean_MessageData_ofConstName(v_constName_1154_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1153_, v___x_1165_, v_constName_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1167_, lean_object* v_constName_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1167_, v_constName_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v_ref_1167_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_ref_1181_; lean_object* v___x_1182_; 
v_ref_1181_ = lean_ctor_get(v___y_1178_, 5);
v___x_1182_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1181_, v_constName_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_env_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; 
v___x_1196_ = lean_st_ref_get(v___y_1194_);
v_env_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_ref(v_env_1197_);
lean_dec(v___x_1196_);
v___x_1198_ = 0;
lean_inc(v_constName_1190_);
v___x_1199_ = l_Lean_Environment_findConstVal_x3f(v_env_1197_, v_constName_1190_, v___x_1198_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1200_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_constName_1190_);
v_val_1201_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1199_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_val_1201_);
lean_dec(v___x_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 0);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_val_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1216_, lean_object* v_us_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1223_; 
lean_inc(v_c_1216_);
v___x_1223_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1216_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v_levelParams_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v_levelParams_1225_ = lean_ctor_get(v_a_1224_, 1);
v___x_1226_ = l_List_lengthTR___redArg(v_levelParams_1225_);
v___x_1227_ = l_List_lengthTR___redArg(v_us_1217_);
v___x_1228_ = lean_nat_dec_eq(v___x_1226_, v___x_1227_);
lean_dec(v___x_1227_);
lean_dec(v___x_1226_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_dec(v_a_1224_);
v___x_1229_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1216_, v_us_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
return v___x_1229_;
}
else
{
lean_object* v___x_1230_; 
lean_dec(v_c_1216_);
v___x_1230_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1224_, v_us_1217_, v_a_1221_);
return v___x_1230_;
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_us_1217_);
lean_dec(v_c_1216_);
v_a_1231_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1223_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1223_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1239_, lean_object* v_us_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1239_, v_us_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_constName_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1255_, v_constName_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1263_, lean_object* v_ref_1264_, lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1264_, v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1272_, v_ref_1273_, v_constName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v_ref_1273_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1281_, lean_object* v_ref_1282_, lean_object* v_msg_1283_, lean_object* v_declHint_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1282_, v_msg_1283_, v_declHint_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_ref_1292_, lean_object* v_msg_1293_, lean_object* v_declHint_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1291_, v_ref_1292_, v_msg_1293_, v_declHint_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v_ref_1292_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1301_, lean_object* v_declHint_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1301_, v_declHint_1302_, v___y_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1309_, lean_object* v_declHint_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1309_, v_declHint_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1317_, lean_object* v_ref_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1318_, v_msg_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_ref_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1326_, v_ref_1327_, v_msg_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_ref_1327_);
return v_res_1334_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1341_, lean_object* v_idx_1342_, lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1352_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1353_ = l_Lean_mkProj(v_structName_1341_, v_idx_1342_, v_e_1343_);
v___x_1354_ = l_Lean_indentExpr(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1352_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_indentExpr(v_a_1344_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1359_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1361_, lean_object* v_idx_1362_, lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_00_u03b1_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1361_, v_idx_1362_, v_e_1363_, v_a_1364_, v_00_u03b1_1365_, v_x_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_env_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = lean_st_ref_get(v___y_1377_);
v_env_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = 0;
lean_inc(v_constName_1373_);
v___x_1382_ = l_Lean_Environment_find_x3f(v_env_1380_, v_constName_1373_, v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_constName_1373_);
v_val_1384_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 0);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1399_, lean_object* v_structName_1400_, lean_object* v_e_1401_, lean_object* v_idx_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_a_1412_; uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_a_1404_, v_upperBound_1399_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_idx_1402_);
lean_dec_ref(v_e_1401_);
lean_dec(v_structName_1400_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1405_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; 
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
v___x_1418_ = lean_whnf(v_b_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
if (lean_obj_tag(v_a_1419_) == 7)
{
lean_object* v_body_1420_; uint8_t v___x_1421_; 
v_body_1420_ = lean_ctor_get(v_a_1419_, 2);
lean_inc_ref(v_body_1420_);
lean_dec_ref_known(v_a_1419_, 3);
v___x_1421_ = l_Lean_Expr_hasLooseBVars(v_body_1420_);
if (v___x_1421_ == 0)
{
v_a_1412_ = v_body_1420_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc_ref(v_e_1401_);
lean_inc(v_a_1404_);
lean_inc(v_structName_1400_);
v___x_1422_ = l_Lean_mkProj(v_structName_1400_, v_a_1404_, v_e_1401_);
v___x_1423_ = lean_expr_instantiate1(v_body_1420_, v___x_1422_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v_body_1420_);
v_a_1412_ = v___x_1423_;
goto v___jp_1411_;
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1401_);
lean_inc(v_idx_1402_);
lean_inc(v_structName_1400_);
v___x_1425_ = l_Lean_mkProj(v_structName_1400_, v_idx_1402_, v_e_1401_);
v___x_1426_ = l_Lean_indentExpr(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1424_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc_ref(v_a_1403_);
v___x_1430_ = l_Lean_indentExpr(v_a_1403_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1431_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref_known(v___x_1432_, 1);
v_a_1412_ = v_a_1419_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_a_1419_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_idx_1402_);
lean_dec_ref(v_e_1401_);
lean_dec(v_structName_1400_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_idx_1402_);
lean_dec_ref(v_e_1401_);
lean_dec(v_structName_1400_);
return v___x_1418_;
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_nat_add(v_a_1404_, v___x_1413_);
lean_dec(v_a_1404_);
v_a_1404_ = v___x_1414_;
v_b_1405_ = v_a_1412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1441_, lean_object* v_structName_1442_, lean_object* v_e_1443_, lean_object* v_idx_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1441_, v_structName_1442_, v_e_1443_, v_idx_1444_, v_a_1445_, v_a_1446_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v_upperBound_1441_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1454_, lean_object* v_structName_1455_, lean_object* v_e_1456_, lean_object* v_idx_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_a_1467_; uint8_t v___x_1471_; 
v___x_1471_ = lean_nat_dec_lt(v_a_1459_, v_upperBound_1454_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_idx_1457_);
lean_dec_ref(v_e_1456_);
lean_dec(v_structName_1455_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_b_1460_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; 
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
v___x_1473_ = lean_whnf(v_b_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
if (lean_obj_tag(v_a_1474_) == 7)
{
lean_object* v_body_1475_; uint8_t v___x_1476_; 
v_body_1475_ = lean_ctor_get(v_a_1474_, 2);
lean_inc_ref(v_body_1475_);
lean_dec_ref_known(v_a_1474_, 3);
v___x_1476_ = l_Lean_Expr_hasLooseBVars(v_body_1475_);
if (v___x_1476_ == 0)
{
v_a_1467_ = v_body_1475_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_inc_ref(v_e_1456_);
lean_inc(v_a_1459_);
lean_inc(v_structName_1455_);
v___x_1477_ = l_Lean_mkProj(v_structName_1455_, v_a_1459_, v_e_1456_);
v___x_1478_ = lean_expr_instantiate1(v_body_1475_, v___x_1477_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v_body_1475_);
v_a_1467_ = v___x_1478_;
goto v___jp_1466_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1479_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1456_);
lean_inc(v_idx_1457_);
lean_inc(v_structName_1455_);
v___x_1480_ = l_Lean_mkProj(v_structName_1455_, v_idx_1457_, v_e_1456_);
v___x_1481_ = l_Lean_indentExpr(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1479_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_inc_ref(v_a_1458_);
v___x_1485_ = l_Lean_indentExpr(v_a_1458_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1486_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec_ref_known(v___x_1487_, 1);
v_a_1467_ = v_a_1474_;
goto v___jp_1466_;
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1474_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_idx_1457_);
lean_dec_ref(v_e_1456_);
lean_dec(v_structName_1455_);
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_idx_1457_);
lean_dec_ref(v_e_1456_);
lean_dec(v_structName_1455_);
return v___x_1473_;
}
}
v___jp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v_a_1459_, v___x_1468_);
lean_dec(v_a_1459_);
v___x_1470_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1454_, v_structName_1455_, v_e_1456_, v_idx_1457_, v_a_1458_, v___x_1469_, v_a_1467_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1496_, lean_object* v_structName_1497_, lean_object* v_e_1498_, lean_object* v_idx_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1496_, v_structName_1497_, v_e_1498_, v_idx_1499_, v_a_1500_, v_a_1501_, v_b_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v_upperBound_1496_);
return v_res_1508_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1509_; lean_object* v_dummy_1510_; 
v___x_1509_ = lean_box(0);
v_dummy_1510_ = l_Lean_Expr_sort___override(v___x_1509_);
return v_dummy_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1511_, lean_object* v_idx_1512_, lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; 
lean_inc(v_a_1517_);
lean_inc_ref(v_a_1516_);
lean_inc(v_a_1515_);
lean_inc_ref(v_a_1514_);
lean_inc_ref(v_e_1513_);
v___x_1519_ = lean_infer_type(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
lean_inc(v_a_1517_);
lean_inc_ref(v_a_1516_);
lean_inc(v_a_1515_);
lean_inc_ref(v_a_1514_);
v___x_1521_ = lean_whnf(v_a_1520_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = l_Lean_Expr_getAppFn(v_a_1522_);
if (lean_obj_tag(v___x_1523_) == 4)
{
lean_object* v_declName_1524_; lean_object* v_us_1525_; lean_object* v___x_1526_; lean_object* v_env_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_declName_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_declName_1524_);
v_us_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_us_1525_);
lean_dec_ref_known(v___x_1523_, 2);
v___x_1526_ = lean_st_ref_get(v_a_1517_);
v_env_1530_ = lean_ctor_get(v___x_1526_, 0);
lean_inc_ref(v_env_1530_);
lean_dec(v___x_1526_);
v___x_1531_ = 0;
v___x_1532_ = l_Lean_Environment_find_x3f(v_env_1530_, v_declName_1524_, v___x_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_us_1525_);
v___x_1533_ = lean_box(0);
v___x_1534_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1533_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1534_;
}
else
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1532_, 1);
if (lean_obj_tag(v_val_1535_) == 5)
{
lean_object* v_val_1536_; lean_object* v_ctors_1537_; 
v_val_1536_ = lean_ctor_get(v_val_1535_, 0);
lean_inc_ref(v_val_1536_);
lean_dec_ref_known(v_val_1535_, 1);
v_ctors_1537_ = lean_ctor_get(v_val_1536_, 4);
lean_inc(v_ctors_1537_);
if (lean_obj_tag(v_ctors_1537_) == 1)
{
lean_object* v_tail_1538_; 
v_tail_1538_ = lean_ctor_get(v_ctors_1537_, 1);
if (lean_obj_tag(v_tail_1538_) == 0)
{
lean_object* v_toConstantVal_1539_; lean_object* v_numParams_1540_; lean_object* v_numIndices_1541_; lean_object* v_head_1542_; lean_object* v___x_1543_; 
v_toConstantVal_1539_ = lean_ctor_get(v_val_1536_, 0);
lean_inc_ref(v_toConstantVal_1539_);
v_numParams_1540_ = lean_ctor_get(v_val_1536_, 1);
lean_inc(v_numParams_1540_);
v_numIndices_1541_ = lean_ctor_get(v_val_1536_, 2);
lean_inc(v_numIndices_1541_);
lean_dec_ref(v_val_1536_);
v_head_1542_ = lean_ctor_get(v_ctors_1537_, 0);
lean_inc(v_head_1542_);
lean_dec_ref_known(v_ctors_1537_, 2);
v___x_1543_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1542_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
if (lean_obj_tag(v_a_1544_) == 6)
{
lean_object* v_val_1545_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_name_1585_; uint8_t v___x_1586_; 
v_val_1545_ = lean_ctor_get(v_a_1544_, 0);
lean_inc_ref(v_val_1545_);
lean_dec_ref_known(v_a_1544_, 1);
v_name_1585_ = lean_ctor_get(v_toConstantVal_1539_, 0);
lean_inc(v_name_1585_);
lean_dec_ref(v_toConstantVal_1539_);
v___x_1586_ = lean_name_eq(v_name_1585_, v_structName_1511_);
lean_dec(v_name_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_val_1545_);
lean_dec(v_numIndices_1541_);
lean_dec(v_numParams_1540_);
lean_dec(v_us_1525_);
v___x_1587_ = lean_box(0);
v___x_1588_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1587_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
v___y_1547_ = v_a_1514_;
v___y_1548_ = v_a_1515_;
v___y_1549_ = v_a_1516_;
v___y_1550_ = v_a_1517_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v_dummy_1551_; lean_object* v_nargs_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_dummy_1551_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1552_ = l_Lean_Expr_getAppNumArgs(v_a_1522_);
lean_inc(v_nargs_1552_);
v___x_1553_ = lean_mk_array(v_nargs_1552_, v_dummy_1551_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_sub(v_nargs_1552_, v___x_1554_);
lean_dec(v_nargs_1552_);
lean_inc(v_a_1522_);
v___x_1556_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1522_, v___x_1553_, v___x_1555_);
v___x_1557_ = lean_nat_add(v_numParams_1540_, v_numIndices_1541_);
lean_dec(v_numIndices_1541_);
v___x_1558_ = lean_array_get_size(v___x_1556_);
v___x_1559_ = lean_nat_dec_eq(v___x_1557_, v___x_1558_);
lean_dec(v___x_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v___x_1556_);
lean_dec_ref(v_val_1545_);
lean_dec(v_numParams_1540_);
lean_dec(v_us_1525_);
v___x_1560_ = lean_box(0);
v___x_1561_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1560_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1561_;
}
else
{
lean_object* v_toConstantVal_1562_; lean_object* v_name_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_toConstantVal_1562_ = lean_ctor_get(v_val_1545_, 0);
lean_inc_ref(v_toConstantVal_1562_);
lean_dec_ref(v_val_1545_);
v_name_1563_ = lean_ctor_get(v_toConstantVal_1562_, 0);
lean_inc(v_name_1563_);
lean_dec_ref(v_toConstantVal_1562_);
v___x_1564_ = l_Lean_mkConst(v_name_1563_, v_us_1525_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = l_Array_toSubarray___redArg(v___x_1556_, v___x_1565_, v_numParams_1540_);
v___x_1567_ = l_Subarray_copy___redArg(v___x_1566_);
v___x_1568_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1564_, v___x_1567_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec_ref(v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
lean_inc(v_a_1522_);
lean_inc_ref(v_e_1513_);
lean_inc(v_structName_1511_);
lean_inc(v_idx_1512_);
v___x_1570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1512_, v_structName_1511_, v_e_1513_, v_idx_1512_, v_a_1522_, v___x_1565_, v_a_1569_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
lean_inc(v___y_1550_);
lean_inc_ref(v___y_1549_);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
v___x_1572_ = lean_whnf(v_a_1571_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1584_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
if (lean_obj_tag(v_a_1573_) == 7)
{
lean_object* v_binderType_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_a_1522_);
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
v_binderType_1577_ = lean_ctor_get(v_a_1573_, 1);
lean_inc_ref(v_binderType_1577_);
lean_dec_ref_known(v_a_1573_, 3);
v___x_1578_ = lean_expr_consume_type_annotations(v_binderType_1577_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_del_object(v___x_1575_);
lean_dec(v_a_1573_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1582_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1583_;
}
}
}
else
{
lean_dec(v_a_1522_);
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
return v___x_1572_;
}
}
else
{
lean_dec(v_a_1522_);
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
return v___x_1570_;
}
}
else
{
lean_dec(v_a_1522_);
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
return v___x_1568_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_a_1544_);
lean_dec(v_numIndices_1541_);
lean_dec(v_numParams_1540_);
lean_dec_ref(v_toConstantVal_1539_);
lean_dec(v_us_1525_);
v___x_1597_ = lean_box(0);
v___x_1598_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1597_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1598_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_numIndices_1541_);
lean_dec(v_numParams_1540_);
lean_dec_ref(v_toConstantVal_1539_);
lean_dec(v_us_1525_);
lean_dec(v_a_1522_);
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
v_a_1599_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1543_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1543_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1537_, 2);
lean_dec_ref(v_val_1536_);
lean_dec(v_us_1525_);
goto v___jp_1527_;
}
}
else
{
lean_dec(v_ctors_1537_);
lean_dec_ref(v_val_1536_);
lean_dec(v_us_1525_);
goto v___jp_1527_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_val_1535_);
lean_dec(v_us_1525_);
v___x_1607_ = lean_box(0);
v___x_1608_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1607_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1608_;
}
}
v___jp_1527_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1528_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1529_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v___x_1523_);
v___x_1609_ = lean_box(0);
v___x_1610_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1511_, v_idx_1512_, v_e_1513_, v_a_1522_, lean_box(0), v___x_1609_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1610_;
}
}
else
{
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
return v___x_1521_;
}
}
else
{
lean_dec_ref(v_e_1513_);
lean_dec(v_idx_1512_);
lean_dec(v_structName_1511_);
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1611_, lean_object* v_idx_1612_, lean_object* v_e_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1611_, v_idx_1612_, v_e_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1620_, lean_object* v_structName_1621_, lean_object* v_e_1622_, lean_object* v_idx_1623_, lean_object* v_a_1624_, lean_object* v_inst_1625_, lean_object* v_R_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_c_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1620_, v_structName_1621_, v_e_1622_, v_idx_1623_, v_a_1624_, v_a_1627_, v_b_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1636_, lean_object* v_structName_1637_, lean_object* v_e_1638_, lean_object* v_idx_1639_, lean_object* v_a_1640_, lean_object* v_inst_1641_, lean_object* v_R_1642_, lean_object* v_a_1643_, lean_object* v_b_1644_, lean_object* v_c_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1636_, v_structName_1637_, v_e_1638_, v_idx_1639_, v_a_1640_, v_inst_1641_, v_R_1642_, v_a_1643_, v_b_1644_, v_c_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v_upperBound_1636_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1652_, lean_object* v_structName_1653_, lean_object* v_e_1654_, lean_object* v_idx_1655_, lean_object* v_a_1656_, lean_object* v_inst_1657_, lean_object* v_R_1658_, lean_object* v_a_1659_, lean_object* v_b_1660_, lean_object* v_c_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1652_, v_structName_1653_, v_e_1654_, v_idx_1655_, v_a_1656_, v_a_1659_, v_b_1660_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1668_, lean_object* v_structName_1669_, lean_object* v_e_1670_, lean_object* v_idx_1671_, lean_object* v_a_1672_, lean_object* v_inst_1673_, lean_object* v_R_1674_, lean_object* v_a_1675_, lean_object* v_b_1676_, lean_object* v_c_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1668_, v_structName_1669_, v_e_1670_, v_idx_1671_, v_a_1672_, v_inst_1673_, v_R_1674_, v_a_1675_, v_b_1676_, v_c_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_upperBound_1668_);
return v_res_1683_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1694_ = l_Lean_indentExpr(v_type_1687_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1695_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1704_, lean_object* v_type_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_type_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1712_, v_type_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_ks_1724_; lean_object* v_vs_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1749_; 
v_ks_1724_ = lean_ctor_get(v_x_1720_, 0);
v_vs_1725_ = lean_ctor_get(v_x_1720_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1720_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1727_ = v_x_1720_;
v_isShared_1728_ = v_isSharedCheck_1749_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_vs_1725_);
lean_inc(v_ks_1724_);
lean_dec(v_x_1720_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1749_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_ks_1724_);
v___x_1730_ = lean_nat_dec_lt(v_x_1721_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec(v_x_1721_);
v___x_1731_ = lean_array_push(v_ks_1724_, v_x_1722_);
v___x_1732_ = lean_array_push(v_vs_1725_, v_x_1723_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1732_);
lean_ctor_set(v___x_1727_, 0, v___x_1731_);
v___x_1734_ = v___x_1727_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_object* v_k_x27_1736_; uint8_t v___x_1737_; 
v_k_x27_1736_ = lean_array_fget_borrowed(v_ks_1724_, v_x_1721_);
v___x_1737_ = l_Lean_instBEqMVarId_beq(v_x_1722_, v_k_x27_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1739_; 
if (v_isShared_1728_ == 0)
{
v___x_1739_ = v___x_1727_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_ks_1724_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_vs_1725_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_x_1721_, v___x_1740_);
lean_dec(v_x_1721_);
v_x_1720_ = v___x_1739_;
v_x_1721_ = v___x_1741_;
goto _start;
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = lean_array_fset(v_ks_1724_, v_x_1721_, v_x_1722_);
v___x_1745_ = lean_array_fset(v_vs_1725_, v_x_1721_, v_x_1723_);
lean_dec(v_x_1721_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1745_);
lean_ctor_set(v___x_1727_, 0, v___x_1744_);
v___x_1747_ = v___x_1727_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1750_, lean_object* v_k_1751_, lean_object* v_v_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1750_, v___x_1753_, v_k_1751_, v_v_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1756_, size_t v_x_1757_, size_t v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v_es_1761_; size_t v___x_1762_; size_t v___x_1763_; lean_object* v_j_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_es_1761_ = lean_ctor_get(v_x_1756_, 0);
v___x_1762_ = ((size_t)31ULL);
v___x_1763_ = lean_usize_land(v_x_1757_, v___x_1762_);
v_j_1764_ = lean_usize_to_nat(v___x_1763_);
v___x_1765_ = lean_array_get_size(v_es_1761_);
v___x_1766_ = lean_nat_dec_lt(v_j_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec(v_j_1764_);
lean_dec(v_x_1760_);
lean_dec(v_x_1759_);
return v_x_1756_;
}
else
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1805_; 
lean_inc_ref(v_es_1761_);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_x_1756_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v_x_1756_, 0);
lean_dec(v_unused_1806_);
v___x_1768_ = v_x_1756_;
v_isShared_1769_ = v_isSharedCheck_1805_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v_x_1756_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1805_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_v_1770_; lean_object* v___x_1771_; lean_object* v_xs_x27_1772_; lean_object* v___y_1774_; 
v_v_1770_ = lean_array_fget(v_es_1761_, v_j_1764_);
v___x_1771_ = lean_box(0);
v_xs_x27_1772_ = lean_array_fset(v_es_1761_, v_j_1764_, v___x_1771_);
switch(lean_obj_tag(v_v_1770_))
{
case 0:
{
lean_object* v_key_1779_; lean_object* v_val_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v_key_1779_ = lean_ctor_get(v_v_1770_, 0);
v_val_1780_ = lean_ctor_get(v_v_1770_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_v_1770_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1782_ = v_v_1770_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_val_1780_);
lean_inc(v_key_1779_);
lean_dec(v_v_1770_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
uint8_t v___x_1784_; 
v___x_1784_ = l_Lean_instBEqMVarId_beq(v_x_1759_, v_key_1779_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_del_object(v___x_1782_);
v___x_1785_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1779_, v_val_1780_, v_x_1759_, v_x_1760_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
v___y_1774_ = v___x_1786_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1788_; 
lean_dec(v_val_1780_);
lean_dec(v_key_1779_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_x_1760_);
lean_ctor_set(v___x_1782_, 0, v_x_1759_);
v___x_1788_ = v___x_1782_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_x_1759_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_x_1760_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v___y_1774_ = v___x_1788_;
goto v___jp_1773_;
}
}
}
}
case 1:
{
lean_object* v_node_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1803_; 
v_node_1791_ = lean_ctor_get(v_v_1770_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_v_1770_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1793_ = v_v_1770_;
v_isShared_1794_ = v_isSharedCheck_1803_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_node_1791_);
lean_dec(v_v_1770_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1803_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1795_ = ((size_t)5ULL);
v___x_1796_ = lean_usize_shift_right(v_x_1757_, v___x_1795_);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_x_1758_, v___x_1797_);
v___x_1799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1791_, v___x_1796_, v___x_1798_, v_x_1759_, v_x_1760_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1799_);
v___x_1801_ = v___x_1793_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
v___y_1774_ = v___x_1801_;
goto v___jp_1773_;
}
}
}
default: 
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_x_1759_);
lean_ctor_set(v___x_1804_, 1, v_x_1760_);
v___y_1774_ = v___x_1804_;
goto v___jp_1773_;
}
}
v___jp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_array_fset(v_xs_x27_1772_, v_j_1764_, v___y_1774_);
lean_dec(v_j_1764_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1775_);
v___x_1777_ = v___x_1768_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
else
{
lean_object* v_ks_1807_; lean_object* v_vs_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1828_; 
v_ks_1807_ = lean_ctor_get(v_x_1756_, 0);
v_vs_1808_ = lean_ctor_get(v_x_1756_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_x_1756_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1810_ = v_x_1756_;
v_isShared_1811_ = v_isSharedCheck_1828_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_vs_1808_);
lean_inc(v_ks_1807_);
lean_dec(v_x_1756_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1828_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_ks_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_vs_1808_);
v___x_1813_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v_newNode_1814_; uint8_t v___y_1816_; size_t v___x_1822_; uint8_t v___x_1823_; 
v_newNode_1814_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1813_, v_x_1759_, v_x_1760_);
v___x_1822_ = ((size_t)7ULL);
v___x_1823_ = lean_usize_dec_le(v___x_1822_, v_x_1758_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1814_);
v___x_1825_ = lean_unsigned_to_nat(4u);
v___x_1826_ = lean_nat_dec_lt(v___x_1824_, v___x_1825_);
lean_dec(v___x_1824_);
v___y_1816_ = v___x_1826_;
goto v___jp_1815_;
}
else
{
v___y_1816_ = v___x_1823_;
goto v___jp_1815_;
}
v___jp_1815_:
{
if (v___y_1816_ == 0)
{
lean_object* v_ks_1817_; lean_object* v_vs_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_ks_1817_ = lean_ctor_get(v_newNode_1814_, 0);
lean_inc_ref(v_ks_1817_);
v_vs_1818_ = lean_ctor_get(v_newNode_1814_, 1);
lean_inc_ref(v_vs_1818_);
lean_dec_ref(v_newNode_1814_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1758_, v_ks_1817_, v_vs_1818_, v___x_1819_, v___x_1820_);
lean_dec_ref(v_vs_1818_);
lean_dec_ref(v_ks_1817_);
return v___x_1821_;
}
else
{
return v_newNode_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1829_, lean_object* v_keys_1830_, lean_object* v_vals_1831_, lean_object* v_i_1832_, lean_object* v_entries_1833_){
_start:
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_array_get_size(v_keys_1830_);
v___x_1835_ = lean_nat_dec_lt(v_i_1832_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_dec(v_i_1832_);
return v_entries_1833_;
}
else
{
lean_object* v_k_1836_; lean_object* v_v_1837_; uint64_t v___x_1838_; size_t v_h_1839_; size_t v___x_1840_; lean_object* v___x_1841_; size_t v___x_1842_; size_t v___x_1843_; size_t v___x_1844_; size_t v_h_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_k_1836_ = lean_array_fget_borrowed(v_keys_1830_, v_i_1832_);
v_v_1837_ = lean_array_fget_borrowed(v_vals_1831_, v_i_1832_);
v___x_1838_ = l_Lean_instHashableMVarId_hash(v_k_1836_);
v_h_1839_ = lean_uint64_to_usize(v___x_1838_);
v___x_1840_ = ((size_t)5ULL);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_sub(v_depth_1829_, v___x_1842_);
v___x_1844_ = lean_usize_mul(v___x_1840_, v___x_1843_);
v_h_1845_ = lean_usize_shift_right(v_h_1839_, v___x_1844_);
v___x_1846_ = lean_nat_add(v_i_1832_, v___x_1841_);
lean_dec(v_i_1832_);
lean_inc(v_v_1837_);
lean_inc(v_k_1836_);
v___x_1847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1833_, v_h_1845_, v_depth_1829_, v_k_1836_, v_v_1837_);
v_i_1832_ = v___x_1846_;
v_entries_1833_ = v___x_1847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1849_, lean_object* v_keys_1850_, lean_object* v_vals_1851_, lean_object* v_i_1852_, lean_object* v_entries_1853_){
_start:
{
size_t v_depth_boxed_1854_; lean_object* v_res_1855_; 
v_depth_boxed_1854_ = lean_unbox_usize(v_depth_1849_);
lean_dec(v_depth_1849_);
v_res_1855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1854_, v_keys_1850_, v_vals_1851_, v_i_1852_, v_entries_1853_);
lean_dec_ref(v_vals_1851_);
lean_dec_ref(v_keys_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
size_t v_x_1230__boxed_1861_; size_t v_x_1231__boxed_1862_; lean_object* v_res_1863_; 
v_x_1230__boxed_1861_ = lean_unbox_usize(v_x_1857_);
lean_dec(v_x_1857_);
v_x_1231__boxed_1862_ = lean_unbox_usize(v_x_1858_);
lean_dec(v_x_1858_);
v_res_1863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1856_, v_x_1230__boxed_1861_, v_x_1231__boxed_1862_, v_x_1859_, v_x_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
uint64_t v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = l_Lean_instHashableMVarId_hash(v_x_1865_);
v___x_1868_ = lean_uint64_to_usize(v___x_1867_);
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1864_, v___x_1868_, v___x_1869_, v_x_1865_, v_x_1866_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1871_, lean_object* v_val_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v_mctx_1876_; lean_object* v_cache_1877_; lean_object* v_zetaDeltaFVarIds_1878_; lean_object* v_postponed_1879_; lean_object* v_diag_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1908_; 
v___x_1875_ = lean_st_ref_take(v___y_1873_);
v_mctx_1876_ = lean_ctor_get(v___x_1875_, 0);
v_cache_1877_ = lean_ctor_get(v___x_1875_, 1);
v_zetaDeltaFVarIds_1878_ = lean_ctor_get(v___x_1875_, 2);
v_postponed_1879_ = lean_ctor_get(v___x_1875_, 3);
v_diag_1880_ = lean_ctor_get(v___x_1875_, 4);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1882_ = v___x_1875_;
v_isShared_1883_ = v_isSharedCheck_1908_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_diag_1880_);
lean_inc(v_postponed_1879_);
lean_inc(v_zetaDeltaFVarIds_1878_);
lean_inc(v_cache_1877_);
lean_inc(v_mctx_1876_);
lean_dec(v___x_1875_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1908_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_depth_1884_; lean_object* v_levelAssignDepth_1885_; lean_object* v_lmvarCounter_1886_; lean_object* v_mvarCounter_1887_; lean_object* v_lDecls_1888_; lean_object* v_decls_1889_; lean_object* v_userNames_1890_; lean_object* v_lAssignment_1891_; lean_object* v_eAssignment_1892_; lean_object* v_dAssignment_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1907_; 
v_depth_1884_ = lean_ctor_get(v_mctx_1876_, 0);
v_levelAssignDepth_1885_ = lean_ctor_get(v_mctx_1876_, 1);
v_lmvarCounter_1886_ = lean_ctor_get(v_mctx_1876_, 2);
v_mvarCounter_1887_ = lean_ctor_get(v_mctx_1876_, 3);
v_lDecls_1888_ = lean_ctor_get(v_mctx_1876_, 4);
v_decls_1889_ = lean_ctor_get(v_mctx_1876_, 5);
v_userNames_1890_ = lean_ctor_get(v_mctx_1876_, 6);
v_lAssignment_1891_ = lean_ctor_get(v_mctx_1876_, 7);
v_eAssignment_1892_ = lean_ctor_get(v_mctx_1876_, 8);
v_dAssignment_1893_ = lean_ctor_get(v_mctx_1876_, 9);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_mctx_1876_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1895_ = v_mctx_1876_;
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_dAssignment_1893_);
lean_inc(v_eAssignment_1892_);
lean_inc(v_lAssignment_1891_);
lean_inc(v_userNames_1890_);
lean_inc(v_decls_1889_);
lean_inc(v_lDecls_1888_);
lean_inc(v_mvarCounter_1887_);
lean_inc(v_lmvarCounter_1886_);
lean_inc(v_levelAssignDepth_1885_);
lean_inc(v_depth_1884_);
lean_dec(v_mctx_1876_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1907_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1892_, v_mvarId_1871_, v_val_1872_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 8, v___x_1897_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_depth_1884_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_levelAssignDepth_1885_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_lmvarCounter_1886_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_mvarCounter_1887_);
lean_ctor_set(v_reuseFailAlloc_1906_, 4, v_lDecls_1888_);
lean_ctor_set(v_reuseFailAlloc_1906_, 5, v_decls_1889_);
lean_ctor_set(v_reuseFailAlloc_1906_, 6, v_userNames_1890_);
lean_ctor_set(v_reuseFailAlloc_1906_, 7, v_lAssignment_1891_);
lean_ctor_set(v_reuseFailAlloc_1906_, 8, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 9, v_dAssignment_1893_);
v___x_1899_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1899_);
v___x_1901_ = v___x_1882_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_cache_1877_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_zetaDeltaFVarIds_1878_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_postponed_1879_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v_diag_1880_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_st_ref_set(v___y_1873_, v___x_1901_);
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
size_t v_x_1583__boxed_2015_; size_t v_x_1584__boxed_2016_; lean_object* v_res_2017_; 
v_x_1583__boxed_2015_ = lean_unbox_usize(v_x_2011_);
lean_dec(v_x_2011_);
v_x_1584__boxed_2016_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_res_2017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2009_, v_x_2010_, v_x_1583__boxed_2015_, v_x_1584__boxed_2016_, v_x_2013_, v_x_2014_);
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
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2612_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2612_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2612_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2558_; lean_object* v_cache_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2607_; 
v___x_2558_ = lean_st_ref_get(v_a_2467_);
v_cache_2559_ = lean_ctor_get(v___x_2558_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; 
v_unused_2608_ = lean_ctor_get(v___x_2558_, 4);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v___x_2558_, 3);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v___x_2558_, 2);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v___x_2558_, 0);
lean_dec(v_unused_2611_);
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2607_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_cache_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2607_;
goto v_resetjp_2560_;
}
v___jp_2516_:
{
lean_object* v___x_2517_; 
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2517_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; uint8_t v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
v___x_2519_ = l_Lean_Expr_hasMVar(v_a_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v___x_2517_, 0);
lean_dec(v_unused_2557_);
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2556_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2517_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2556_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_cache_2524_; lean_object* v_mctx_2525_; lean_object* v_zetaDeltaFVarIds_2526_; lean_object* v_postponed_2527_; lean_object* v_diag_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2555_; 
v___x_2523_ = lean_st_ref_take(v_a_2467_);
v_cache_2524_ = lean_ctor_get(v___x_2523_, 1);
v_mctx_2525_ = lean_ctor_get(v___x_2523_, 0);
v_zetaDeltaFVarIds_2526_ = lean_ctor_get(v___x_2523_, 2);
v_postponed_2527_ = lean_ctor_get(v___x_2523_, 3);
v_diag_2528_ = lean_ctor_get(v___x_2523_, 4);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2555_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_diag_2528_);
lean_inc(v_postponed_2527_);
lean_inc(v_zetaDeltaFVarIds_2526_);
lean_inc(v_cache_2524_);
lean_inc(v_mctx_2525_);
lean_dec(v___x_2523_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2555_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_inferType_2532_; lean_object* v_funInfo_2533_; lean_object* v_synthInstance_2534_; lean_object* v_whnf_2535_; lean_object* v_defEqTrans_2536_; lean_object* v_defEqPerm_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2554_; 
v_inferType_2532_ = lean_ctor_get(v_cache_2524_, 0);
v_funInfo_2533_ = lean_ctor_get(v_cache_2524_, 1);
v_synthInstance_2534_ = lean_ctor_get(v_cache_2524_, 2);
v_whnf_2535_ = lean_ctor_get(v_cache_2524_, 3);
v_defEqTrans_2536_ = lean_ctor_get(v_cache_2524_, 4);
v_defEqPerm_2537_ = lean_ctor_get(v_cache_2524_, 5);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_cache_2524_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2539_ = v_cache_2524_;
v_isShared_2540_ = v_isSharedCheck_2554_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_defEqPerm_2537_);
lean_inc(v_defEqTrans_2536_);
lean_inc(v_whnf_2535_);
lean_inc(v_synthInstance_2534_);
lean_inc(v_funInfo_2533_);
lean_inc(v_inferType_2532_);
lean_dec(v_cache_2524_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2554_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___f_2541_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2542_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2518_);
v___x_2543_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2541_, v___x_2542_, v_inferType_2532_, v_a_2512_, v_a_2518_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2543_);
v___x_2545_ = v___x_2539_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_funInfo_2533_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_synthInstance_2534_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_whnf_2535_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_defEqTrans_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v_defEqPerm_2537_);
v___x_2545_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2545_);
v___x_2547_ = v___x_2530_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_mctx_2525_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_zetaDeltaFVarIds_2526_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_postponed_2527_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_diag_2528_);
v___x_2547_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_st_ref_set(v_a_2467_, v___x_2547_);
if (v_isShared_2522_ == 0)
{
v___x_2550_ = v___x_2521_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2518_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2518_);
lean_dec(v_a_2512_);
return v___x_2517_;
}
}
else
{
lean_dec(v_a_2512_);
return v___x_2517_;
}
}
v_resetjp_2560_:
{
lean_object* v_inferType_2563_; lean_object* v___f_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_inferType_2563_ = lean_ctor_get(v_cache_2559_, 0);
lean_inc_ref(v_inferType_2563_);
lean_dec_ref(v_cache_2559_);
v___f_2564_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2512_);
v___x_2566_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2564_, v___x_2565_, v_inferType_2563_, v_a_2512_);
lean_dec_ref(v_inferType_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; lean_object* v_toApplicative_2568_; lean_object* v_toFunctor_2569_; lean_object* v_toSeq_2570_; lean_object* v_toSeqLeft_2571_; lean_object* v_toSeqRight_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2582_; 
lean_del_object(v___x_2514_);
v___x_2567_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2568_ = lean_ctor_get(v___x_2567_, 0);
v_toFunctor_2569_ = lean_ctor_get(v_toApplicative_2568_, 0);
v_toSeq_2570_ = lean_ctor_get(v_toApplicative_2568_, 2);
v_toSeqLeft_2571_ = lean_ctor_get(v_toApplicative_2568_, 3);
v_toSeqRight_2572_ = lean_ctor_get(v_toApplicative_2568_, 4);
v___f_2573_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2574_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2569_, 2);
v___f_2575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2575_, 0, v_toFunctor_2569_);
v___f_2576_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2576_, 0, v_toFunctor_2569_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___f_2575_);
lean_ctor_set(v___x_2577_, 1, v___f_2576_);
lean_inc(v_toSeqRight_2572_);
v___f_2578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2578_, 0, v_toSeqRight_2572_);
lean_inc(v_toSeqLeft_2571_);
v___f_2579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2579_, 0, v_toSeqLeft_2571_);
lean_inc(v_toSeq_2570_);
v___f_2580_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2580_, 0, v_toSeq_2570_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 4, v___f_2578_);
lean_ctor_set(v___x_2561_, 3, v___f_2579_);
lean_ctor_set(v___x_2561_, 2, v___f_2580_);
lean_ctor_set(v___x_2561_, 1, v___f_2573_);
lean_ctor_set(v___x_2561_, 0, v___x_2577_);
v___x_2582_ = v___x_2561_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v___f_2573_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v___f_2580_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v___f_2579_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v___f_2578_);
v___x_2582_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v_cancelTk_x3f_2584_; 
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___f_2574_);
v_cancelTk_x3f_2584_ = lean_ctor_get(v_a_2468_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2584_) == 1)
{
lean_object* v_val_2585_; uint8_t v___x_2586_; 
v_val_2585_ = lean_ctor_get(v_cancelTk_x3f_2584_, 0);
v___x_2586_ = l_IO_CancelToken_isSet(v_val_2585_);
if (v___x_2586_ == 0)
{
lean_dec_ref_known(v___x_2583_, 2);
goto v___jp_2516_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2392__overap_2592_; lean_object* v___x_2593_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2588_ = l_Lean_Core_instMonadRefCoreM;
v___x_2589_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2590_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2589_, v___x_2583_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2588_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
v___x_2392__overap_2592_ = l_Lean_throwInterruptException___redArg(v___x_2591_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2593_ = lean_apply_3(v___x_2392__overap_2592_, v_a_2468_, v_a_2469_, lean_box(0));
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_dec_ref_known(v___x_2593_, 1);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2512_);
lean_dec_ref(v_inferType_2465_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2583_, 2);
goto v___jp_2516_;
}
}
}
else
{
lean_object* v_val_2603_; lean_object* v___x_2605_; 
lean_del_object(v___x_2561_);
lean_dec(v_a_2512_);
lean_dec_ref(v_inferType_2465_);
v_val_2603_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2566_, 1);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v_val_2603_);
v___x_2605_ = v___x_2514_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_val_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_inferType_2465_);
v_a_2613_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2511_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2511_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
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
lean_object* v___x_2472_; lean_object* v_toApplicative_2473_; lean_object* v_toFunctor_2474_; lean_object* v_toSeq_2475_; lean_object* v_toSeqLeft_2476_; lean_object* v_toSeqRight_2477_; lean_object* v___f_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_cancelTk_x3f_2488_; 
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
v_cancelTk_x3f_2488_ = lean_ctor_get(v_a_2468_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2488_) == 1)
{
lean_object* v_val_2489_; uint8_t v___x_2490_; 
v_val_2489_ = lean_ctor_get(v_cancelTk_x3f_2488_, 0);
v___x_2490_ = l_IO_CancelToken_isSet(v_val_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref_known(v___x_2487_, 2);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2491_ = lean_apply_5(v_inferType_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2189__overap_2497_; lean_object* v___x_2498_; 
v___x_2492_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2493_ = l_Lean_Core_instMonadRefCoreM;
v___x_2494_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2495_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2494_, v___x_2487_);
v___x_2496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2492_);
lean_ctor_set(v___x_2496_, 1, v___x_2493_);
lean_ctor_set(v___x_2496_, 2, v___x_2495_);
v___x_2189__overap_2497_ = l_Lean_throwInterruptException___redArg(v___x_2496_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
v___x_2498_ = lean_apply_3(v___x_2189__overap_2497_, v_a_2468_, v_a_2469_, lean_box(0));
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
lean_dec_ref_known(v___x_2487_, 2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2621_, lean_object* v_inferType_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2621_, v_inferType_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___y_2636_; uint8_t v___y_2637_; uint8_t v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2675_; lean_object* v___x_2733_; uint8_t v_transparency_2734_; uint8_t v___x_2735_; uint8_t v___x_2736_; 
v___x_2733_ = l_Lean_Meta_Context_config(v_a_2630_);
v_transparency_2734_ = lean_ctor_get_uint8(v___x_2733_, 9);
lean_dec_ref(v___x_2733_);
v___x_2735_ = 1;
v___x_2736_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2734_, v___x_2735_);
if (v___x_2736_ == 0)
{
v___y_2675_ = v_transparency_2734_;
goto v___jp_2674_;
}
else
{
v___y_2675_ = v___x_2735_;
goto v___jp_2674_;
}
v___jp_2635_:
{
lean_object* v___x_2647_; uint8_t v_foApprox_2648_; uint8_t v_ctxApprox_2649_; uint8_t v_quasiPatternApprox_2650_; uint8_t v_constApprox_2651_; uint8_t v_isDefEqStuckEx_2652_; uint8_t v_unificationHints_2653_; uint8_t v_proofIrrelevance_2654_; uint8_t v_assignSyntheticOpaque_2655_; uint8_t v_offsetCnstrs_2656_; uint8_t v_transparency_2657_; uint8_t v_univApprox_2658_; uint8_t v_zetaUnused_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2673_; 
v___x_2647_ = l_Lean_Meta_Context_config(v___y_2636_);
lean_dec_ref(v___y_2636_);
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
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2661_ = v___x_2647_;
v_isShared_2662_ = v_isSharedCheck_2673_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2647_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2673_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; uint8_t v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2667_; 
v___x_2663_ = 1;
v___x_2664_ = 0;
v___x_2665_ = 2;
if (v_isShared_2662_ == 0)
{
v___x_2667_ = v___x_2661_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 0, v_foApprox_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 1, v_ctxApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 2, v_quasiPatternApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 3, v_constApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 4, v_isDefEqStuckEx_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 5, v_unificationHints_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 6, v_proofIrrelevance_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 7, v_assignSyntheticOpaque_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 8, v_offsetCnstrs_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 9, v_transparency_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 11, v_univApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 17, v_zetaUnused_2659_);
v___x_2667_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
uint64_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_ctor_set_uint8(v___x_2667_, 10, v___x_2664_);
lean_ctor_set_uint8(v___x_2667_, 12, v___x_2663_);
lean_ctor_set_uint8(v___x_2667_, 13, v___x_2663_);
lean_ctor_set_uint8(v___x_2667_, 14, v___x_2665_);
lean_ctor_set_uint8(v___x_2667_, 15, v___x_2663_);
lean_ctor_set_uint8(v___x_2667_, 16, v___x_2663_);
lean_ctor_set_uint8(v___x_2667_, 18, v___x_2663_);
v___x_2668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set_uint64(v___x_2669_, sizeof(void*)*1, v___x_2668_);
lean_inc(v___y_2644_);
lean_inc(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2645_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2646_);
v___x_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___y_2646_);
lean_ctor_set(v___x_2670_, 2, v___y_2642_);
lean_ctor_set(v___x_2670_, 3, v___y_2645_);
lean_ctor_set(v___x_2670_, 4, v___y_2640_);
lean_ctor_set(v___x_2670_, 5, v___y_2641_);
lean_ctor_set(v___x_2670_, 6, v___y_2644_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7, v___y_2639_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 1, v___y_2638_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 2, v___y_2637_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 3, v___y_2643_);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
v___x_2671_ = lean_apply_5(v_x_2629_, v___x_2670_, v_a_2631_, v_a_2632_, v_a_2633_, lean_box(0));
return v___x_2671_;
}
}
}
v___jp_2674_:
{
lean_object* v___x_2676_; uint8_t v_foApprox_2677_; uint8_t v_ctxApprox_2678_; uint8_t v_quasiPatternApprox_2679_; uint8_t v_constApprox_2680_; uint8_t v_isDefEqStuckEx_2681_; uint8_t v_unificationHints_2682_; uint8_t v_proofIrrelevance_2683_; uint8_t v_assignSyntheticOpaque_2684_; uint8_t v_offsetCnstrs_2685_; uint8_t v_etaStruct_2686_; uint8_t v_univApprox_2687_; uint8_t v_iota_2688_; uint8_t v_beta_2689_; uint8_t v_proj_2690_; uint8_t v_zeta_2691_; uint8_t v_zetaDelta_2692_; uint8_t v_zetaUnused_2693_; uint8_t v_zetaHave_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2732_; 
v___x_2676_ = l_Lean_Meta_Context_config(v_a_2630_);
v_foApprox_2677_ = lean_ctor_get_uint8(v___x_2676_, 0);
v_ctxApprox_2678_ = lean_ctor_get_uint8(v___x_2676_, 1);
v_quasiPatternApprox_2679_ = lean_ctor_get_uint8(v___x_2676_, 2);
v_constApprox_2680_ = lean_ctor_get_uint8(v___x_2676_, 3);
v_isDefEqStuckEx_2681_ = lean_ctor_get_uint8(v___x_2676_, 4);
v_unificationHints_2682_ = lean_ctor_get_uint8(v___x_2676_, 5);
v_proofIrrelevance_2683_ = lean_ctor_get_uint8(v___x_2676_, 6);
v_assignSyntheticOpaque_2684_ = lean_ctor_get_uint8(v___x_2676_, 7);
v_offsetCnstrs_2685_ = lean_ctor_get_uint8(v___x_2676_, 8);
v_etaStruct_2686_ = lean_ctor_get_uint8(v___x_2676_, 10);
v_univApprox_2687_ = lean_ctor_get_uint8(v___x_2676_, 11);
v_iota_2688_ = lean_ctor_get_uint8(v___x_2676_, 12);
v_beta_2689_ = lean_ctor_get_uint8(v___x_2676_, 13);
v_proj_2690_ = lean_ctor_get_uint8(v___x_2676_, 14);
v_zeta_2691_ = lean_ctor_get_uint8(v___x_2676_, 15);
v_zetaDelta_2692_ = lean_ctor_get_uint8(v___x_2676_, 16);
v_zetaUnused_2693_ = lean_ctor_get_uint8(v___x_2676_, 17);
v_zetaHave_2694_ = lean_ctor_get_uint8(v___x_2676_, 18);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2696_ = v___x_2676_;
v_isShared_2697_ = v_isSharedCheck_2732_;
goto v_resetjp_2695_;
}
else
{
lean_dec(v___x_2676_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2732_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v_trackZetaDelta_2698_; lean_object* v_zetaDeltaSet_2699_; lean_object* v_lctx_2700_; lean_object* v_localInstances_2701_; lean_object* v_defEqCtx_x3f_2702_; lean_object* v_synthPendingDepth_2703_; lean_object* v_canUnfold_x3f_2704_; uint8_t v_univApprox_2705_; uint8_t v_inTypeClassResolution_2706_; uint8_t v_cacheInferType_2707_; lean_object* v_config_2709_; 
v_trackZetaDelta_2698_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7);
v_zetaDeltaSet_2699_ = lean_ctor_get(v_a_2630_, 1);
v_lctx_2700_ = lean_ctor_get(v_a_2630_, 2);
v_localInstances_2701_ = lean_ctor_get(v_a_2630_, 3);
v_defEqCtx_x3f_2702_ = lean_ctor_get(v_a_2630_, 4);
v_synthPendingDepth_2703_ = lean_ctor_get(v_a_2630_, 5);
v_canUnfold_x3f_2704_ = lean_ctor_get(v_a_2630_, 6);
v_univApprox_2705_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2706_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 2);
v_cacheInferType_2707_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*7 + 3);
if (v_isShared_2697_ == 0)
{
v_config_2709_ = v___x_2696_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 0, v_foApprox_2677_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 1, v_ctxApprox_2678_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 2, v_quasiPatternApprox_2679_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 3, v_constApprox_2680_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 4, v_isDefEqStuckEx_2681_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 5, v_unificationHints_2682_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 6, v_proofIrrelevance_2683_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 7, v_assignSyntheticOpaque_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 8, v_offsetCnstrs_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 10, v_etaStruct_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 11, v_univApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 12, v_iota_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 13, v_beta_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 14, v_proj_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 15, v_zeta_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 16, v_zetaDelta_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 17, v_zetaUnused_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, 18, v_zetaHave_2694_);
v_config_2709_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
uint64_t v___x_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; uint64_t v___x_2714_; uint64_t v_key_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v_beta_2719_; 
lean_ctor_set_uint8(v_config_2709_, 9, v___y_2675_);
v___x_2710_ = l_Lean_Meta_Context_configKey(v_a_2630_);
v___x_2711_ = 3ULL;
v___x_2712_ = lean_uint64_shift_right(v___x_2710_, v___x_2711_);
v___x_2713_ = lean_uint64_shift_left(v___x_2712_, v___x_2711_);
v___x_2714_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2675_);
v_key_2715_ = lean_uint64_lor(v___x_2713_, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2716_, 0, v_config_2709_);
lean_ctor_set_uint64(v___x_2716_, sizeof(void*)*1, v_key_2715_);
lean_inc(v_canUnfold_x3f_2704_);
lean_inc(v_synthPendingDepth_2703_);
lean_inc(v_defEqCtx_x3f_2702_);
lean_inc_ref(v_localInstances_2701_);
lean_inc_ref(v_lctx_2700_);
lean_inc(v_zetaDeltaSet_2699_);
v___x_2717_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_zetaDeltaSet_2699_);
lean_ctor_set(v___x_2717_, 2, v_lctx_2700_);
lean_ctor_set(v___x_2717_, 3, v_localInstances_2701_);
lean_ctor_set(v___x_2717_, 4, v_defEqCtx_x3f_2702_);
lean_ctor_set(v___x_2717_, 5, v_synthPendingDepth_2703_);
lean_ctor_set(v___x_2717_, 6, v_canUnfold_x3f_2704_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*7, v_trackZetaDelta_2698_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*7 + 1, v_univApprox_2705_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2706_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*7 + 3, v_cacheInferType_2707_);
v___x_2718_ = l_Lean_Meta_Context_config(v___x_2717_);
v_beta_2719_ = lean_ctor_get_uint8(v___x_2718_, 13);
if (v_beta_2719_ == 0)
{
lean_dec_ref(v___x_2718_);
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v_iota_2720_; 
v_iota_2720_ = lean_ctor_get_uint8(v___x_2718_, 12);
if (v_iota_2720_ == 0)
{
lean_dec_ref(v___x_2718_);
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v_zeta_2721_; 
v_zeta_2721_ = lean_ctor_get_uint8(v___x_2718_, 15);
if (v_zeta_2721_ == 0)
{
lean_dec_ref(v___x_2718_);
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v_zetaHave_2722_; 
v_zetaHave_2722_ = lean_ctor_get_uint8(v___x_2718_, 18);
if (v_zetaHave_2722_ == 0)
{
lean_dec_ref(v___x_2718_);
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v_zetaDelta_2723_; 
v_zetaDelta_2723_ = lean_ctor_get_uint8(v___x_2718_, 16);
if (v_zetaDelta_2723_ == 0)
{
lean_dec_ref(v___x_2718_);
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v_etaStruct_2724_; uint8_t v_proj_2725_; uint8_t v___x_2726_; uint8_t v___x_2727_; 
v_etaStruct_2724_ = lean_ctor_get_uint8(v___x_2718_, 10);
v_proj_2725_ = lean_ctor_get_uint8(v___x_2718_, 14);
lean_dec_ref(v___x_2718_);
v___x_2726_ = 2;
v___x_2727_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
uint8_t v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = 0;
v___x_2729_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2724_, v___x_2728_);
if (v___x_2729_ == 0)
{
v___y_2636_ = v___x_2717_;
v___y_2637_ = v_inTypeClassResolution_2706_;
v___y_2638_ = v_univApprox_2705_;
v___y_2639_ = v_trackZetaDelta_2698_;
v___y_2640_ = v_defEqCtx_x3f_2702_;
v___y_2641_ = v_synthPendingDepth_2703_;
v___y_2642_ = v_lctx_2700_;
v___y_2643_ = v_cacheInferType_2707_;
v___y_2644_ = v_canUnfold_x3f_2704_;
v___y_2645_ = v_localInstances_2701_;
v___y_2646_ = v_zetaDeltaSet_2699_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2730_; 
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
v___x_2730_ = lean_apply_5(v_x_2629_, v___x_2717_, v_a_2631_, v_a_2632_, v_a_2633_, lean_box(0));
return v___x_2730_;
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
lean_object* v___y_2752_; uint8_t v___y_2753_; uint8_t v___y_2754_; uint8_t v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; uint8_t v___y_2791_; lean_object* v___x_2849_; uint8_t v_transparency_2850_; uint8_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2849_ = l_Lean_Meta_Context_config(v_a_2746_);
v_transparency_2850_ = lean_ctor_get_uint8(v___x_2849_, 9);
lean_dec_ref(v___x_2849_);
v___x_2851_ = 1;
v___x_2852_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
v___y_2791_ = v_transparency_2850_;
goto v___jp_2790_;
}
else
{
v___y_2791_ = v___x_2851_;
goto v___jp_2790_;
}
v___jp_2751_:
{
lean_object* v___x_2763_; uint8_t v_foApprox_2764_; uint8_t v_ctxApprox_2765_; uint8_t v_quasiPatternApprox_2766_; uint8_t v_constApprox_2767_; uint8_t v_isDefEqStuckEx_2768_; uint8_t v_unificationHints_2769_; uint8_t v_proofIrrelevance_2770_; uint8_t v_assignSyntheticOpaque_2771_; uint8_t v_offsetCnstrs_2772_; uint8_t v_transparency_2773_; uint8_t v_univApprox_2774_; uint8_t v_zetaUnused_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2789_; 
v___x_2763_ = l_Lean_Meta_Context_config(v___y_2752_);
lean_dec_ref(v___y_2752_);
v_foApprox_2764_ = lean_ctor_get_uint8(v___x_2763_, 0);
v_ctxApprox_2765_ = lean_ctor_get_uint8(v___x_2763_, 1);
v_quasiPatternApprox_2766_ = lean_ctor_get_uint8(v___x_2763_, 2);
v_constApprox_2767_ = lean_ctor_get_uint8(v___x_2763_, 3);
v_isDefEqStuckEx_2768_ = lean_ctor_get_uint8(v___x_2763_, 4);
v_unificationHints_2769_ = lean_ctor_get_uint8(v___x_2763_, 5);
v_proofIrrelevance_2770_ = lean_ctor_get_uint8(v___x_2763_, 6);
v_assignSyntheticOpaque_2771_ = lean_ctor_get_uint8(v___x_2763_, 7);
v_offsetCnstrs_2772_ = lean_ctor_get_uint8(v___x_2763_, 8);
v_transparency_2773_ = lean_ctor_get_uint8(v___x_2763_, 9);
v_univApprox_2774_ = lean_ctor_get_uint8(v___x_2763_, 11);
v_zetaUnused_2775_ = lean_ctor_get_uint8(v___x_2763_, 17);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2777_ = v___x_2763_;
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v___x_2763_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
uint8_t v___x_2779_; uint8_t v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2783_; 
v___x_2779_ = 1;
v___x_2780_ = 0;
v___x_2781_ = 2;
if (v_isShared_2778_ == 0)
{
v___x_2783_ = v___x_2777_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 0, v_foApprox_2764_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 1, v_ctxApprox_2765_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 2, v_quasiPatternApprox_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 3, v_constApprox_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 4, v_isDefEqStuckEx_2768_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 5, v_unificationHints_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 6, v_proofIrrelevance_2770_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 7, v_assignSyntheticOpaque_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 8, v_offsetCnstrs_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 9, v_transparency_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 11, v_univApprox_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, 17, v_zetaUnused_2775_);
v___x_2783_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
uint64_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_ctor_set_uint8(v___x_2783_, 10, v___x_2780_);
lean_ctor_set_uint8(v___x_2783_, 12, v___x_2779_);
lean_ctor_set_uint8(v___x_2783_, 13, v___x_2779_);
lean_ctor_set_uint8(v___x_2783_, 14, v___x_2781_);
lean_ctor_set_uint8(v___x_2783_, 15, v___x_2779_);
lean_ctor_set_uint8(v___x_2783_, 16, v___x_2779_);
lean_ctor_set_uint8(v___x_2783_, 18, v___x_2779_);
v___x_2784_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set_uint64(v___x_2785_, sizeof(void*)*1, v___x_2784_);
lean_inc(v___y_2760_);
lean_inc(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2761_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2762_);
v___x_2786_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___y_2762_);
lean_ctor_set(v___x_2786_, 2, v___y_2758_);
lean_ctor_set(v___x_2786_, 3, v___y_2761_);
lean_ctor_set(v___x_2786_, 4, v___y_2756_);
lean_ctor_set(v___x_2786_, 5, v___y_2757_);
lean_ctor_set(v___x_2786_, 6, v___y_2760_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7, v___y_2755_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 1, v___y_2754_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 2, v___y_2753_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*7 + 3, v___y_2759_);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
v___x_2787_ = lean_apply_5(v_x_2745_, v___x_2786_, v_a_2747_, v_a_2748_, v_a_2749_, lean_box(0));
return v___x_2787_;
}
}
}
v___jp_2790_:
{
lean_object* v___x_2792_; uint8_t v_foApprox_2793_; uint8_t v_ctxApprox_2794_; uint8_t v_quasiPatternApprox_2795_; uint8_t v_constApprox_2796_; uint8_t v_isDefEqStuckEx_2797_; uint8_t v_unificationHints_2798_; uint8_t v_proofIrrelevance_2799_; uint8_t v_assignSyntheticOpaque_2800_; uint8_t v_offsetCnstrs_2801_; uint8_t v_etaStruct_2802_; uint8_t v_univApprox_2803_; uint8_t v_iota_2804_; uint8_t v_beta_2805_; uint8_t v_proj_2806_; uint8_t v_zeta_2807_; uint8_t v_zetaDelta_2808_; uint8_t v_zetaUnused_2809_; uint8_t v_zetaHave_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2848_; 
v___x_2792_ = l_Lean_Meta_Context_config(v_a_2746_);
v_foApprox_2793_ = lean_ctor_get_uint8(v___x_2792_, 0);
v_ctxApprox_2794_ = lean_ctor_get_uint8(v___x_2792_, 1);
v_quasiPatternApprox_2795_ = lean_ctor_get_uint8(v___x_2792_, 2);
v_constApprox_2796_ = lean_ctor_get_uint8(v___x_2792_, 3);
v_isDefEqStuckEx_2797_ = lean_ctor_get_uint8(v___x_2792_, 4);
v_unificationHints_2798_ = lean_ctor_get_uint8(v___x_2792_, 5);
v_proofIrrelevance_2799_ = lean_ctor_get_uint8(v___x_2792_, 6);
v_assignSyntheticOpaque_2800_ = lean_ctor_get_uint8(v___x_2792_, 7);
v_offsetCnstrs_2801_ = lean_ctor_get_uint8(v___x_2792_, 8);
v_etaStruct_2802_ = lean_ctor_get_uint8(v___x_2792_, 10);
v_univApprox_2803_ = lean_ctor_get_uint8(v___x_2792_, 11);
v_iota_2804_ = lean_ctor_get_uint8(v___x_2792_, 12);
v_beta_2805_ = lean_ctor_get_uint8(v___x_2792_, 13);
v_proj_2806_ = lean_ctor_get_uint8(v___x_2792_, 14);
v_zeta_2807_ = lean_ctor_get_uint8(v___x_2792_, 15);
v_zetaDelta_2808_ = lean_ctor_get_uint8(v___x_2792_, 16);
v_zetaUnused_2809_ = lean_ctor_get_uint8(v___x_2792_, 17);
v_zetaHave_2810_ = lean_ctor_get_uint8(v___x_2792_, 18);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2812_ = v___x_2792_;
v_isShared_2813_ = v_isSharedCheck_2848_;
goto v_resetjp_2811_;
}
else
{
lean_dec(v___x_2792_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2848_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
uint8_t v_trackZetaDelta_2814_; lean_object* v_zetaDeltaSet_2815_; lean_object* v_lctx_2816_; lean_object* v_localInstances_2817_; lean_object* v_defEqCtx_x3f_2818_; lean_object* v_synthPendingDepth_2819_; lean_object* v_canUnfold_x3f_2820_; uint8_t v_univApprox_2821_; uint8_t v_inTypeClassResolution_2822_; uint8_t v_cacheInferType_2823_; lean_object* v_config_2825_; 
v_trackZetaDelta_2814_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7);
v_zetaDeltaSet_2815_ = lean_ctor_get(v_a_2746_, 1);
v_lctx_2816_ = lean_ctor_get(v_a_2746_, 2);
v_localInstances_2817_ = lean_ctor_get(v_a_2746_, 3);
v_defEqCtx_x3f_2818_ = lean_ctor_get(v_a_2746_, 4);
v_synthPendingDepth_2819_ = lean_ctor_get(v_a_2746_, 5);
v_canUnfold_x3f_2820_ = lean_ctor_get(v_a_2746_, 6);
v_univApprox_2821_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2822_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 2);
v_cacheInferType_2823_ = lean_ctor_get_uint8(v_a_2746_, sizeof(void*)*7 + 3);
if (v_isShared_2813_ == 0)
{
v_config_2825_ = v___x_2812_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 0, v_foApprox_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 1, v_ctxApprox_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 2, v_quasiPatternApprox_2795_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 3, v_constApprox_2796_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 4, v_isDefEqStuckEx_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 5, v_unificationHints_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 6, v_proofIrrelevance_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 7, v_assignSyntheticOpaque_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 8, v_offsetCnstrs_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 10, v_etaStruct_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 11, v_univApprox_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 12, v_iota_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 13, v_beta_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 14, v_proj_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 15, v_zeta_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 16, v_zetaDelta_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 17, v_zetaUnused_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2847_, 18, v_zetaHave_2810_);
v_config_2825_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
uint64_t v___x_2826_; uint64_t v___x_2827_; uint64_t v___x_2828_; uint64_t v___x_2829_; uint64_t v___x_2830_; uint64_t v_key_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v_beta_2835_; 
lean_ctor_set_uint8(v_config_2825_, 9, v___y_2791_);
v___x_2826_ = l_Lean_Meta_Context_configKey(v_a_2746_);
v___x_2827_ = 3ULL;
v___x_2828_ = lean_uint64_shift_right(v___x_2826_, v___x_2827_);
v___x_2829_ = lean_uint64_shift_left(v___x_2828_, v___x_2827_);
v___x_2830_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2791_);
v_key_2831_ = lean_uint64_lor(v___x_2829_, v___x_2830_);
v___x_2832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2832_, 0, v_config_2825_);
lean_ctor_set_uint64(v___x_2832_, sizeof(void*)*1, v_key_2831_);
lean_inc(v_canUnfold_x3f_2820_);
lean_inc(v_synthPendingDepth_2819_);
lean_inc(v_defEqCtx_x3f_2818_);
lean_inc_ref(v_localInstances_2817_);
lean_inc_ref(v_lctx_2816_);
lean_inc(v_zetaDeltaSet_2815_);
v___x_2833_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v_zetaDeltaSet_2815_);
lean_ctor_set(v___x_2833_, 2, v_lctx_2816_);
lean_ctor_set(v___x_2833_, 3, v_localInstances_2817_);
lean_ctor_set(v___x_2833_, 4, v_defEqCtx_x3f_2818_);
lean_ctor_set(v___x_2833_, 5, v_synthPendingDepth_2819_);
lean_ctor_set(v___x_2833_, 6, v_canUnfold_x3f_2820_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*7, v_trackZetaDelta_2814_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*7 + 1, v_univApprox_2821_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2822_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*7 + 3, v_cacheInferType_2823_);
v___x_2834_ = l_Lean_Meta_Context_config(v___x_2833_);
v_beta_2835_ = lean_ctor_get_uint8(v___x_2834_, 13);
if (v_beta_2835_ == 0)
{
lean_dec_ref(v___x_2834_);
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v_iota_2836_; 
v_iota_2836_ = lean_ctor_get_uint8(v___x_2834_, 12);
if (v_iota_2836_ == 0)
{
lean_dec_ref(v___x_2834_);
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v_zeta_2837_; 
v_zeta_2837_ = lean_ctor_get_uint8(v___x_2834_, 15);
if (v_zeta_2837_ == 0)
{
lean_dec_ref(v___x_2834_);
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v_zetaHave_2838_; 
v_zetaHave_2838_ = lean_ctor_get_uint8(v___x_2834_, 18);
if (v_zetaHave_2838_ == 0)
{
lean_dec_ref(v___x_2834_);
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v_zetaDelta_2839_; 
v_zetaDelta_2839_ = lean_ctor_get_uint8(v___x_2834_, 16);
if (v_zetaDelta_2839_ == 0)
{
lean_dec_ref(v___x_2834_);
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v_etaStruct_2840_; uint8_t v_proj_2841_; uint8_t v___x_2842_; uint8_t v___x_2843_; 
v_etaStruct_2840_ = lean_ctor_get_uint8(v___x_2834_, 10);
v_proj_2841_ = lean_ctor_get_uint8(v___x_2834_, 14);
lean_dec_ref(v___x_2834_);
v___x_2842_ = 2;
v___x_2843_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
uint8_t v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = 0;
v___x_2845_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2840_, v___x_2844_);
if (v___x_2845_ == 0)
{
v___y_2752_ = v___x_2833_;
v___y_2753_ = v_inTypeClassResolution_2822_;
v___y_2754_ = v_univApprox_2821_;
v___y_2755_ = v_trackZetaDelta_2814_;
v___y_2756_ = v_defEqCtx_x3f_2818_;
v___y_2757_ = v_synthPendingDepth_2819_;
v___y_2758_ = v_lctx_2816_;
v___y_2759_ = v_cacheInferType_2823_;
v___y_2760_ = v_canUnfold_x3f_2820_;
v___y_2761_ = v_localInstances_2817_;
v___y_2762_ = v_zetaDeltaSet_2815_;
goto v___jp_2751_;
}
else
{
lean_object* v___x_2846_; 
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
v___x_2846_ = lean_apply_5(v_x_2745_, v___x_2833_, v_a_2747_, v_a_2748_, v_a_2749_, lean_box(0));
return v___x_2846_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2853_, lean_object* v_x_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2853_, v_x_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
return v_res_2860_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_box(0);
v___x_2862_ = l_Lean_interruptExceptionId;
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v___x_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
lean_object* v_ks_2883_; lean_object* v_vs_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2913_; 
v_ks_2883_ = lean_ctor_get(v_x_2879_, 0);
v_vs_2884_ = lean_ctor_get(v_x_2879_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2886_ = v_x_2879_;
v_isShared_2887_ = v_isSharedCheck_2913_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_vs_2884_);
lean_inc(v_ks_2883_);
lean_dec(v_x_2879_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2913_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v___y_2889_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = lean_array_get_size(v_ks_2883_);
v___x_2902_ = lean_nat_dec_lt(v_x_2880_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
lean_del_object(v___x_2886_);
lean_dec(v_x_2880_);
v___x_2903_ = lean_array_push(v_ks_2883_, v_x_2881_);
v___x_2904_ = lean_array_push(v_vs_2884_, v_x_2882_);
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
return v___x_2905_;
}
else
{
lean_object* v_expr_2906_; uint64_t v_configKey_2907_; lean_object* v_k_x27_2908_; lean_object* v_expr_2909_; uint64_t v_configKey_2910_; uint8_t v___x_2911_; 
v_expr_2906_ = lean_ctor_get(v_x_2881_, 0);
v_configKey_2907_ = lean_ctor_get_uint64(v_x_2881_, sizeof(void*)*1);
v_k_x27_2908_ = lean_array_fget_borrowed(v_ks_2883_, v_x_2880_);
v_expr_2909_ = lean_ctor_get(v_k_x27_2908_, 0);
v_configKey_2910_ = lean_ctor_get_uint64(v_k_x27_2908_, sizeof(void*)*1);
v___x_2911_ = lean_expr_equal(v_expr_2906_, v_expr_2909_);
if (v___x_2911_ == 0)
{
v___y_2889_ = v___x_2911_;
goto v___jp_2888_;
}
else
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_uint64_dec_eq(v_configKey_2907_, v_configKey_2910_);
v___y_2889_ = v___x_2912_;
goto v___jp_2888_;
}
}
v___jp_2888_:
{
if (v___y_2889_ == 0)
{
lean_object* v___x_2891_; 
if (v_isShared_2887_ == 0)
{
v___x_2891_ = v___x_2886_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_ks_2883_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_vs_2884_);
v___x_2891_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_add(v_x_2880_, v___x_2892_);
lean_dec(v_x_2880_);
v_x_2879_ = v___x_2891_;
v_x_2880_ = v___x_2893_;
goto _start;
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = lean_array_fset(v_ks_2883_, v_x_2880_, v_x_2881_);
v___x_2897_ = lean_array_fset(v_vs_2884_, v_x_2880_, v_x_2882_);
lean_dec(v_x_2880_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v___x_2897_);
lean_ctor_set(v___x_2886_, 0, v___x_2896_);
v___x_2899_ = v___x_2886_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2914_, lean_object* v_k_2915_, lean_object* v_v_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2914_, v___x_2917_, v_k_2915_, v_v_2916_);
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2920_, size_t v_x_2921_, size_t v_x_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
if (lean_obj_tag(v_x_2920_) == 0)
{
lean_object* v_es_2925_; size_t v___x_2926_; size_t v___x_2927_; lean_object* v_j_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v_es_2925_ = lean_ctor_get(v_x_2920_, 0);
v___x_2926_ = ((size_t)31ULL);
v___x_2927_ = lean_usize_land(v_x_2921_, v___x_2926_);
v_j_2928_ = lean_usize_to_nat(v___x_2927_);
v___x_2929_ = lean_array_get_size(v_es_2925_);
v___x_2930_ = lean_nat_dec_lt(v_j_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_dec(v_j_2928_);
lean_dec(v_x_2924_);
lean_dec_ref(v_x_2923_);
return v_x_2920_;
}
else
{
lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2976_; 
lean_inc_ref(v_es_2925_);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_x_2920_, 0);
lean_dec(v_unused_2977_);
v___x_2932_ = v_x_2920_;
v_isShared_2933_ = v_isSharedCheck_2976_;
goto v_resetjp_2931_;
}
else
{
lean_dec(v_x_2920_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2976_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_v_2934_; lean_object* v___x_2935_; lean_object* v_xs_x27_2936_; lean_object* v___y_2938_; 
v_v_2934_ = lean_array_fget(v_es_2925_, v_j_2928_);
v___x_2935_ = lean_box(0);
v_xs_x27_2936_ = lean_array_fset(v_es_2925_, v_j_2928_, v___x_2935_);
switch(lean_obj_tag(v_v_2934_))
{
case 0:
{
lean_object* v_key_2943_; lean_object* v_val_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2961_; 
v_key_2943_ = lean_ctor_get(v_v_2934_, 0);
v_val_2944_ = lean_ctor_get(v_v_2934_, 1);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_v_2934_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2946_ = v_v_2934_;
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_val_2944_);
lean_inc(v_key_2943_);
lean_dec(v_v_2934_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2961_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
uint8_t v___y_2949_; lean_object* v_expr_2955_; uint64_t v_configKey_2956_; lean_object* v_expr_2957_; uint64_t v_configKey_2958_; uint8_t v___x_2959_; 
v_expr_2955_ = lean_ctor_get(v_x_2923_, 0);
v_configKey_2956_ = lean_ctor_get_uint64(v_x_2923_, sizeof(void*)*1);
v_expr_2957_ = lean_ctor_get(v_key_2943_, 0);
v_configKey_2958_ = lean_ctor_get_uint64(v_key_2943_, sizeof(void*)*1);
v___x_2959_ = lean_expr_equal(v_expr_2955_, v_expr_2957_);
if (v___x_2959_ == 0)
{
v___y_2949_ = v___x_2959_;
goto v___jp_2948_;
}
else
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_uint64_dec_eq(v_configKey_2956_, v_configKey_2958_);
v___y_2949_ = v___x_2960_;
goto v___jp_2948_;
}
v___jp_2948_:
{
if (v___y_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_del_object(v___x_2946_);
v___x_2950_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2943_, v_val_2944_, v_x_2923_, v_x_2924_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
v___y_2938_ = v___x_2951_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2953_; 
lean_dec(v_val_2944_);
lean_dec(v_key_2943_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_x_2924_);
lean_ctor_set(v___x_2946_, 0, v_x_2923_);
v___x_2953_ = v___x_2946_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_x_2923_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_x_2924_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
v___y_2938_ = v___x_2953_;
goto v___jp_2937_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2974_; 
v_node_2962_ = lean_ctor_get(v_v_2934_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_v_2934_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2964_ = v_v_2934_;
v_isShared_2965_ = v_isSharedCheck_2974_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_node_2962_);
lean_dec(v_v_2934_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2974_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
size_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2966_ = ((size_t)5ULL);
v___x_2967_ = lean_usize_shift_right(v_x_2921_, v___x_2966_);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_x_2922_, v___x_2968_);
v___x_2970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2962_, v___x_2967_, v___x_2969_, v_x_2923_, v_x_2924_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2970_);
v___x_2972_ = v___x_2964_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v___y_2938_ = v___x_2972_;
goto v___jp_2937_;
}
}
}
default: 
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_x_2923_);
lean_ctor_set(v___x_2975_, 1, v_x_2924_);
v___y_2938_ = v___x_2975_;
goto v___jp_2937_;
}
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_array_fset(v_xs_x27_2936_, v_j_2928_, v___y_2938_);
lean_dec(v_j_2928_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2939_);
v___x_2941_ = v___x_2932_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_object* v_ks_2978_; lean_object* v_vs_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2999_; 
v_ks_2978_ = lean_ctor_get(v_x_2920_, 0);
v_vs_2979_ = lean_ctor_get(v_x_2920_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_x_2920_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2981_ = v_x_2920_;
v_isShared_2982_ = v_isSharedCheck_2999_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_vs_2979_);
lean_inc(v_ks_2978_);
lean_dec(v_x_2920_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2999_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_ks_2978_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_vs_2979_);
v___x_2984_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v_newNode_2985_; uint8_t v___y_2987_; size_t v___x_2993_; uint8_t v___x_2994_; 
v_newNode_2985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2984_, v_x_2923_, v_x_2924_);
v___x_2993_ = ((size_t)7ULL);
v___x_2994_ = lean_usize_dec_le(v___x_2993_, v_x_2922_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2985_);
v___x_2996_ = lean_unsigned_to_nat(4u);
v___x_2997_ = lean_nat_dec_lt(v___x_2995_, v___x_2996_);
lean_dec(v___x_2995_);
v___y_2987_ = v___x_2997_;
goto v___jp_2986_;
}
else
{
v___y_2987_ = v___x_2994_;
goto v___jp_2986_;
}
v___jp_2986_:
{
if (v___y_2987_ == 0)
{
lean_object* v_ks_2988_; lean_object* v_vs_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_ks_2988_ = lean_ctor_get(v_newNode_2985_, 0);
lean_inc_ref(v_ks_2988_);
v_vs_2989_ = lean_ctor_get(v_newNode_2985_, 1);
lean_inc_ref(v_vs_2989_);
lean_dec_ref(v_newNode_2985_);
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2922_, v_ks_2988_, v_vs_2989_, v___x_2990_, v___x_2991_);
lean_dec_ref(v_vs_2989_);
lean_dec_ref(v_ks_2988_);
return v___x_2992_;
}
else
{
return v_newNode_2985_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3000_, lean_object* v_keys_3001_, lean_object* v_vals_3002_, lean_object* v_i_3003_, lean_object* v_entries_3004_){
_start:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = lean_array_get_size(v_keys_3001_);
v___x_3006_ = lean_nat_dec_lt(v_i_3003_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec(v_i_3003_);
return v_entries_3004_;
}
else
{
lean_object* v_k_3007_; lean_object* v_expr_3008_; uint64_t v_configKey_3009_; lean_object* v_v_3010_; uint64_t v___x_3011_; uint64_t v___x_3012_; size_t v_h_3013_; size_t v___x_3014_; lean_object* v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; size_t v___x_3018_; size_t v_h_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_k_3007_ = lean_array_fget_borrowed(v_keys_3001_, v_i_3003_);
v_expr_3008_ = lean_ctor_get(v_k_3007_, 0);
v_configKey_3009_ = lean_ctor_get_uint64(v_k_3007_, sizeof(void*)*1);
v_v_3010_ = lean_array_fget_borrowed(v_vals_3002_, v_i_3003_);
v___x_3011_ = l_Lean_Expr_hash(v_expr_3008_);
v___x_3012_ = lean_uint64_mix_hash(v___x_3011_, v_configKey_3009_);
v_h_3013_ = lean_uint64_to_usize(v___x_3012_);
v___x_3014_ = ((size_t)5ULL);
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = ((size_t)1ULL);
v___x_3017_ = lean_usize_sub(v_depth_3000_, v___x_3016_);
v___x_3018_ = lean_usize_mul(v___x_3014_, v___x_3017_);
v_h_3019_ = lean_usize_shift_right(v_h_3013_, v___x_3018_);
v___x_3020_ = lean_nat_add(v_i_3003_, v___x_3015_);
lean_dec(v_i_3003_);
lean_inc(v_v_3010_);
lean_inc(v_k_3007_);
v___x_3021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3004_, v_h_3019_, v_depth_3000_, v_k_3007_, v_v_3010_);
v_i_3003_ = v___x_3020_;
v_entries_3004_ = v___x_3021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3023_, lean_object* v_keys_3024_, lean_object* v_vals_3025_, lean_object* v_i_3026_, lean_object* v_entries_3027_){
_start:
{
size_t v_depth_boxed_3028_; lean_object* v_res_3029_; 
v_depth_boxed_3028_ = lean_unbox_usize(v_depth_3023_);
lean_dec(v_depth_3023_);
v_res_3029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3028_, v_keys_3024_, v_vals_3025_, v_i_3026_, v_entries_3027_);
lean_dec_ref(v_vals_3025_);
lean_dec_ref(v_keys_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
size_t v_x_2762__boxed_3035_; size_t v_x_2763__boxed_3036_; lean_object* v_res_3037_; 
v_x_2762__boxed_3035_ = lean_unbox_usize(v_x_3031_);
lean_dec(v_x_3031_);
v_x_2763__boxed_3036_ = lean_unbox_usize(v_x_3032_);
lean_dec(v_x_3032_);
v_res_3037_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3030_, v_x_2762__boxed_3035_, v_x_2763__boxed_3036_, v_x_3033_, v_x_3034_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v_expr_3041_; uint64_t v_configKey_3042_; uint64_t v___x_3043_; uint64_t v___x_3044_; size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v_expr_3041_ = lean_ctor_get(v_x_3039_, 0);
v_configKey_3042_ = lean_ctor_get_uint64(v_x_3039_, sizeof(void*)*1);
v___x_3043_ = l_Lean_Expr_hash(v_expr_3041_);
v___x_3044_ = lean_uint64_mix_hash(v___x_3043_, v_configKey_3042_);
v___x_3045_ = lean_uint64_to_usize(v___x_3044_);
v___x_3046_ = ((size_t)1ULL);
v___x_3047_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3038_, v___x_3045_, v___x_3046_, v_x_3039_, v_x_3040_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3048_, lean_object* v_vals_3049_, lean_object* v_i_3050_, lean_object* v_k_3051_){
_start:
{
uint8_t v___y_3053_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = lean_array_get_size(v_keys_3048_);
v___x_3060_ = lean_nat_dec_lt(v_i_3050_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec(v_i_3050_);
v___x_3061_ = lean_box(0);
return v___x_3061_;
}
else
{
lean_object* v_expr_3062_; uint64_t v_configKey_3063_; lean_object* v_k_x27_3064_; lean_object* v_expr_3065_; uint64_t v_configKey_3066_; uint8_t v___x_3067_; 
v_expr_3062_ = lean_ctor_get(v_k_3051_, 0);
v_configKey_3063_ = lean_ctor_get_uint64(v_k_3051_, sizeof(void*)*1);
v_k_x27_3064_ = lean_array_fget_borrowed(v_keys_3048_, v_i_3050_);
v_expr_3065_ = lean_ctor_get(v_k_x27_3064_, 0);
v_configKey_3066_ = lean_ctor_get_uint64(v_k_x27_3064_, sizeof(void*)*1);
v___x_3067_ = lean_expr_equal(v_expr_3062_, v_expr_3065_);
if (v___x_3067_ == 0)
{
v___y_3053_ = v___x_3067_;
goto v___jp_3052_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_uint64_dec_eq(v_configKey_3063_, v_configKey_3066_);
v___y_3053_ = v___x_3068_;
goto v___jp_3052_;
}
}
v___jp_3052_:
{
if (v___y_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(1u);
v___x_3055_ = lean_nat_add(v_i_3050_, v___x_3054_);
lean_dec(v_i_3050_);
v_i_3050_ = v___x_3055_;
goto _start;
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_array_fget_borrowed(v_vals_3049_, v_i_3050_);
lean_dec(v_i_3050_);
lean_inc(v___x_3057_);
v___x_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3069_, lean_object* v_vals_3070_, lean_object* v_i_3071_, lean_object* v_k_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3069_, v_vals_3070_, v_i_3071_, v_k_3072_);
lean_dec_ref(v_k_3072_);
lean_dec_ref(v_vals_3070_);
lean_dec_ref(v_keys_3069_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3074_, size_t v_x_3075_, lean_object* v_x_3076_){
_start:
{
if (lean_obj_tag(v_x_3074_) == 0)
{
lean_object* v_es_3077_; lean_object* v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v_j_3081_; lean_object* v___x_3082_; 
v_es_3077_ = lean_ctor_get(v_x_3074_, 0);
v___x_3078_ = lean_box(2);
v___x_3079_ = ((size_t)31ULL);
v___x_3080_ = lean_usize_land(v_x_3075_, v___x_3079_);
v_j_3081_ = lean_usize_to_nat(v___x_3080_);
v___x_3082_ = lean_array_get_borrowed(v___x_3078_, v_es_3077_, v_j_3081_);
lean_dec(v_j_3081_);
switch(lean_obj_tag(v___x_3082_))
{
case 0:
{
lean_object* v_key_3083_; lean_object* v_val_3084_; uint8_t v___y_3086_; lean_object* v_expr_3089_; uint64_t v_configKey_3090_; lean_object* v_expr_3091_; uint64_t v_configKey_3092_; uint8_t v___x_3093_; 
v_key_3083_ = lean_ctor_get(v___x_3082_, 0);
v_val_3084_ = lean_ctor_get(v___x_3082_, 1);
v_expr_3089_ = lean_ctor_get(v_x_3076_, 0);
v_configKey_3090_ = lean_ctor_get_uint64(v_x_3076_, sizeof(void*)*1);
v_expr_3091_ = lean_ctor_get(v_key_3083_, 0);
v_configKey_3092_ = lean_ctor_get_uint64(v_key_3083_, sizeof(void*)*1);
v___x_3093_ = lean_expr_equal(v_expr_3089_, v_expr_3091_);
if (v___x_3093_ == 0)
{
v___y_3086_ = v___x_3093_;
goto v___jp_3085_;
}
else
{
uint8_t v___x_3094_; 
v___x_3094_ = lean_uint64_dec_eq(v_configKey_3090_, v_configKey_3092_);
v___y_3086_ = v___x_3094_;
goto v___jp_3085_;
}
v___jp_3085_:
{
if (v___y_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_box(0);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
lean_inc(v_val_3084_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_val_3084_);
return v___x_3088_;
}
}
}
case 1:
{
lean_object* v_node_3095_; size_t v___x_3096_; size_t v___x_3097_; 
v_node_3095_ = lean_ctor_get(v___x_3082_, 0);
v___x_3096_ = ((size_t)5ULL);
v___x_3097_ = lean_usize_shift_right(v_x_3075_, v___x_3096_);
v_x_3074_ = v_node_3095_;
v_x_3075_ = v___x_3097_;
goto _start;
}
default: 
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
}
}
else
{
lean_object* v_ks_3100_; lean_object* v_vs_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_ks_3100_ = lean_ctor_get(v_x_3074_, 0);
v_vs_3101_ = lean_ctor_get(v_x_3074_, 1);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3100_, v_vs_3101_, v___x_3102_, v_x_3076_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_){
_start:
{
size_t v_x_2971__boxed_3107_; lean_object* v_res_3108_; 
v_x_2971__boxed_3107_ = lean_unbox_usize(v_x_3105_);
lean_dec(v_x_3105_);
v_res_3108_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3104_, v_x_2971__boxed_3107_, v_x_3106_);
lean_dec_ref(v_x_3106_);
lean_dec_ref(v_x_3104_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v_expr_3111_; uint64_t v_configKey_3112_; uint64_t v___x_3113_; uint64_t v___x_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v_expr_3111_ = lean_ctor_get(v_x_3110_, 0);
v_configKey_3112_ = lean_ctor_get_uint64(v_x_3110_, sizeof(void*)*1);
v___x_3113_ = l_Lean_Expr_hash(v_expr_3111_);
v___x_3114_ = lean_uint64_mix_hash(v___x_3113_, v_configKey_3112_);
v___x_3115_ = lean_uint64_to_usize(v___x_3114_);
v___x_3116_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3109_, v___x_3115_, v_x_3110_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3117_, lean_object* v_x_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3117_, v_x_3118_);
lean_dec_ref(v_x_3118_);
lean_dec_ref(v_x_3117_);
return v_res_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3122_ = l_Lean_stringToMessageData(v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
switch(lean_obj_tag(v_e_3123_))
{
case 0:
{
lean_object* v_deBruijnIndex_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_deBruijnIndex_3159_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_deBruijnIndex_3159_);
lean_dec_ref_known(v_e_3123_, 1);
v___x_3160_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3161_ = l_Lean_mkBVar(v_deBruijnIndex_3159_);
v___x_3162_ = l_Lean_MessageData_ofExpr(v___x_3161_);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3160_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3163_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3164_;
}
case 1:
{
lean_object* v_fvarId_3165_; lean_object* v___x_3166_; 
v_fvarId_3165_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_fvarId_3165_);
lean_dec_ref_known(v_e_3123_, 1);
v___x_3166_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3165_, v_a_3124_, v_a_3126_, v_a_3127_);
return v___x_3166_;
}
case 2:
{
lean_object* v_mvarId_3167_; lean_object* v___x_3168_; 
v_mvarId_3167_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_mvarId_3167_);
lean_dec_ref_known(v_e_3123_, 1);
v___x_3168_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3167_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3168_;
}
case 3:
{
lean_object* v_u_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_u_3169_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_u_3169_);
lean_dec_ref_known(v_e_3123_, 1);
v___x_3170_ = l_Lean_Level_succ___override(v_u_3169_);
v___x_3171_ = l_Lean_mkSort(v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
case 4:
{
lean_object* v_declName_3173_; lean_object* v_us_3174_; 
v_declName_3173_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_declName_3173_);
v_us_3174_ = lean_ctor_get(v_e_3123_, 1);
lean_inc(v_us_3174_);
if (lean_obj_tag(v_us_3174_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref_known(v_e_3123_, 2);
v___x_3190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3173_, v_us_3174_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3190_;
}
else
{
uint8_t v_cacheInferType_3191_; 
v_cacheInferType_3191_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3191_ == 0)
{
lean_dec_ref_known(v_e_3123_, 2);
goto v___jp_3175_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = l_Lean_Expr_hasMVar(v_e_3123_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3258_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3258_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3258_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3238_; lean_object* v_cache_3239_; lean_object* v_inferType_3240_; lean_object* v___x_3241_; 
v___x_3238_ = lean_st_ref_get(v_a_3125_);
v_cache_3239_ = lean_ctor_get(v___x_3238_, 1);
lean_inc_ref(v_cache_3239_);
lean_dec(v___x_3238_);
v_inferType_3240_ = lean_ctor_get(v_cache_3239_, 0);
lean_inc_ref(v_inferType_3240_);
lean_dec_ref(v_cache_3239_);
v___x_3241_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3240_, v_a_3194_);
lean_dec_ref(v_inferType_3240_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_cancelTk_x3f_3242_; 
lean_del_object(v___x_3196_);
v_cancelTk_x3f_3242_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3242_) == 1)
{
lean_object* v_val_3243_; uint8_t v___x_3244_; 
v_val_3243_ = lean_ctor_get(v_cancelTk_x3f_3242_, 0);
v___x_3244_ = l_IO_CancelToken_isSet(v_val_3243_);
if (v___x_3244_ == 0)
{
goto v___jp_3198_;
}
else
{
lean_object* v___x_3245_; lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_a_3194_);
lean_dec(v_us_3174_);
lean_dec(v_declName_3173_);
v___x_3245_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
goto v___jp_3198_;
}
}
else
{
lean_object* v_val_3254_; lean_object* v___x_3256_; 
lean_dec(v_a_3194_);
lean_dec(v_us_3174_);
lean_dec(v_declName_3173_);
v_val_3254_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v___x_3241_, 1);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v_val_3254_);
v___x_3256_ = v___x_3196_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_val_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
v___jp_3198_:
{
lean_object* v___x_3199_; 
v___x_3199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3173_, v_us_3174_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; uint8_t v___x_3201_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
v___x_3201_ = l_Lean_Expr_hasMVar(v_a_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3237_);
v___x_3203_ = v___x_3199_;
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v___x_3199_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3236_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v_cache_3206_; lean_object* v_mctx_3207_; lean_object* v_zetaDeltaFVarIds_3208_; lean_object* v_postponed_3209_; lean_object* v_diag_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3235_; 
v___x_3205_ = lean_st_ref_take(v_a_3125_);
v_cache_3206_ = lean_ctor_get(v___x_3205_, 1);
v_mctx_3207_ = lean_ctor_get(v___x_3205_, 0);
v_zetaDeltaFVarIds_3208_ = lean_ctor_get(v___x_3205_, 2);
v_postponed_3209_ = lean_ctor_get(v___x_3205_, 3);
v_diag_3210_ = lean_ctor_get(v___x_3205_, 4);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3212_ = v___x_3205_;
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_diag_3210_);
lean_inc(v_postponed_3209_);
lean_inc(v_zetaDeltaFVarIds_3208_);
lean_inc(v_cache_3206_);
lean_inc(v_mctx_3207_);
lean_dec(v___x_3205_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_inferType_3214_; lean_object* v_funInfo_3215_; lean_object* v_synthInstance_3216_; lean_object* v_whnf_3217_; lean_object* v_defEqTrans_3218_; lean_object* v_defEqPerm_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3234_; 
v_inferType_3214_ = lean_ctor_get(v_cache_3206_, 0);
v_funInfo_3215_ = lean_ctor_get(v_cache_3206_, 1);
v_synthInstance_3216_ = lean_ctor_get(v_cache_3206_, 2);
v_whnf_3217_ = lean_ctor_get(v_cache_3206_, 3);
v_defEqTrans_3218_ = lean_ctor_get(v_cache_3206_, 4);
v_defEqPerm_3219_ = lean_ctor_get(v_cache_3206_, 5);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_cache_3206_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3221_ = v_cache_3206_;
v_isShared_3222_ = v_isSharedCheck_3234_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_defEqPerm_3219_);
lean_inc(v_defEqTrans_3218_);
lean_inc(v_whnf_3217_);
lean_inc(v_synthInstance_3216_);
lean_inc(v_funInfo_3215_);
lean_inc(v_inferType_3214_);
lean_dec(v_cache_3206_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3234_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_inc(v_a_3200_);
v___x_3223_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3214_, v_a_3194_, v_a_3200_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_funInfo_3215_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_synthInstance_3216_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_whnf_3217_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_defEqTrans_3218_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v_defEqPerm_3219_);
v___x_3225_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3227_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 1, v___x_3225_);
v___x_3227_ = v___x_3212_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_mctx_3207_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_zetaDeltaFVarIds_3208_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_postponed_3209_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_diag_3210_);
v___x_3227_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_st_ref_set(v_a_3125_, v___x_3227_);
if (v_isShared_3204_ == 0)
{
v___x_3230_ = v___x_3203_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3200_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3200_);
lean_dec(v_a_3194_);
return v___x_3199_;
}
}
else
{
lean_dec(v_a_3194_);
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_us_3174_);
lean_dec(v_declName_3173_);
v_a_3259_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3193_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3193_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3123_, 2);
goto v___jp_3175_;
}
}
}
v___jp_3175_:
{
lean_object* v_cancelTk_x3f_3176_; 
v_cancelTk_x3f_3176_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3176_) == 1)
{
lean_object* v_val_3177_; uint8_t v___x_3178_; 
v_val_3177_ = lean_ctor_get(v_cancelTk_x3f_3176_, 0);
v___x_3178_ = l_IO_CancelToken_isSet(v_val_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3173_, v_us_3174_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_us_3174_);
lean_dec(v_declName_3173_);
v___x_3180_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v___x_3189_; 
v___x_3189_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3173_, v_us_3174_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3189_;
}
}
}
case 5:
{
lean_object* v_fn_3267_; uint8_t v_cacheInferType_3268_; lean_object* v_nargs_3269_; lean_object* v___x_3270_; lean_object* v_dummy_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_fn_3267_ = lean_ctor_get(v_e_3123_, 0);
v_cacheInferType_3268_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*7 + 3);
v_nargs_3269_ = l_Lean_Expr_getAppNumArgs(v_e_3123_);
v___x_3270_ = l_Lean_Expr_getAppFn(v_fn_3267_);
v_dummy_3271_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3269_);
v___x_3272_ = lean_mk_array(v_nargs_3269_, v_dummy_3271_);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_sub(v_nargs_3269_, v___x_3273_);
lean_dec(v_nargs_3269_);
lean_inc_ref(v_e_3123_);
v___x_3275_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3123_, v___x_3272_, v___x_3274_);
if (v_cacheInferType_3268_ == 0)
{
lean_dec_ref_known(v_e_3123_, 2);
goto v___jp_3276_;
}
else
{
uint8_t v___x_3291_; 
v___x_3291_ = l_Lean_Expr_hasMVar(v_e_3123_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3357_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3357_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3357_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3337_; lean_object* v_cache_3338_; lean_object* v_inferType_3339_; lean_object* v___x_3340_; 
v___x_3337_ = lean_st_ref_get(v_a_3125_);
v_cache_3338_ = lean_ctor_get(v___x_3337_, 1);
lean_inc_ref(v_cache_3338_);
lean_dec(v___x_3337_);
v_inferType_3339_ = lean_ctor_get(v_cache_3338_, 0);
lean_inc_ref(v_inferType_3339_);
lean_dec_ref(v_cache_3338_);
v___x_3340_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3339_, v_a_3293_);
lean_dec_ref(v_inferType_3339_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_cancelTk_x3f_3341_; 
lean_del_object(v___x_3295_);
v_cancelTk_x3f_3341_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3341_) == 1)
{
lean_object* v_val_3342_; uint8_t v___x_3343_; 
v_val_3342_ = lean_ctor_get(v_cancelTk_x3f_3341_, 0);
v___x_3343_ = l_IO_CancelToken_isSet(v_val_3342_);
if (v___x_3343_ == 0)
{
goto v___jp_3297_;
}
else
{
lean_object* v___x_3344_; lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3293_);
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___x_3270_);
v___x_3344_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
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
else
{
goto v___jp_3297_;
}
}
else
{
lean_object* v_val_3353_; lean_object* v___x_3355_; 
lean_dec(v_a_3293_);
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___x_3270_);
v_val_3353_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_val_3353_);
lean_dec_ref_known(v___x_3340_, 1);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v_val_3353_);
v___x_3355_ = v___x_3295_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_val_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
v___jp_3297_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3270_, v___x_3275_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec_ref(v___x_3275_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; uint8_t v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
v___x_3300_ = l_Lean_Expr_hasMVar(v_a_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3335_; 
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v___x_3298_, 0);
lean_dec(v_unused_3336_);
v___x_3302_ = v___x_3298_;
v_isShared_3303_ = v_isSharedCheck_3335_;
goto v_resetjp_3301_;
}
else
{
lean_dec(v___x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3335_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v_cache_3305_; lean_object* v_mctx_3306_; lean_object* v_zetaDeltaFVarIds_3307_; lean_object* v_postponed_3308_; lean_object* v_diag_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3334_; 
v___x_3304_ = lean_st_ref_take(v_a_3125_);
v_cache_3305_ = lean_ctor_get(v___x_3304_, 1);
v_mctx_3306_ = lean_ctor_get(v___x_3304_, 0);
v_zetaDeltaFVarIds_3307_ = lean_ctor_get(v___x_3304_, 2);
v_postponed_3308_ = lean_ctor_get(v___x_3304_, 3);
v_diag_3309_ = lean_ctor_get(v___x_3304_, 4);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3311_ = v___x_3304_;
v_isShared_3312_ = v_isSharedCheck_3334_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_diag_3309_);
lean_inc(v_postponed_3308_);
lean_inc(v_zetaDeltaFVarIds_3307_);
lean_inc(v_cache_3305_);
lean_inc(v_mctx_3306_);
lean_dec(v___x_3304_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3334_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_inferType_3313_; lean_object* v_funInfo_3314_; lean_object* v_synthInstance_3315_; lean_object* v_whnf_3316_; lean_object* v_defEqTrans_3317_; lean_object* v_defEqPerm_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3333_; 
v_inferType_3313_ = lean_ctor_get(v_cache_3305_, 0);
v_funInfo_3314_ = lean_ctor_get(v_cache_3305_, 1);
v_synthInstance_3315_ = lean_ctor_get(v_cache_3305_, 2);
v_whnf_3316_ = lean_ctor_get(v_cache_3305_, 3);
v_defEqTrans_3317_ = lean_ctor_get(v_cache_3305_, 4);
v_defEqPerm_3318_ = lean_ctor_get(v_cache_3305_, 5);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_cache_3305_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3320_ = v_cache_3305_;
v_isShared_3321_ = v_isSharedCheck_3333_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_defEqPerm_3318_);
lean_inc(v_defEqTrans_3317_);
lean_inc(v_whnf_3316_);
lean_inc(v_synthInstance_3315_);
lean_inc(v_funInfo_3314_);
lean_inc(v_inferType_3313_);
lean_dec(v_cache_3305_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3333_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_inc(v_a_3299_);
v___x_3322_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3313_, v_a_3293_, v_a_3299_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v___x_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_funInfo_3314_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_synthInstance_3315_);
lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_whnf_3316_);
lean_ctor_set(v_reuseFailAlloc_3332_, 4, v_defEqTrans_3317_);
lean_ctor_set(v_reuseFailAlloc_3332_, 5, v_defEqPerm_3318_);
v___x_3324_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3326_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v___x_3324_);
v___x_3326_ = v___x_3311_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_mctx_3306_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3331_, 2, v_zetaDeltaFVarIds_3307_);
lean_ctor_set(v_reuseFailAlloc_3331_, 3, v_postponed_3308_);
lean_ctor_set(v_reuseFailAlloc_3331_, 4, v_diag_3309_);
v___x_3326_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3327_ = lean_st_ref_set(v_a_3125_, v___x_3326_);
if (v_isShared_3303_ == 0)
{
v___x_3329_ = v___x_3302_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3299_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3299_);
lean_dec(v_a_3293_);
return v___x_3298_;
}
}
else
{
lean_dec(v_a_3293_);
return v___x_3298_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___x_3270_);
v_a_3358_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3292_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3292_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3123_, 2);
goto v___jp_3276_;
}
}
v___jp_3276_:
{
lean_object* v_cancelTk_x3f_3277_; 
v_cancelTk_x3f_3277_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3277_) == 1)
{
lean_object* v_val_3278_; uint8_t v___x_3279_; 
v_val_3278_ = lean_ctor_get(v_cancelTk_x3f_3277_, 0);
v___x_3279_ = l_IO_CancelToken_isSet(v_val_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3270_, v___x_3275_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec_ref(v___x_3275_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___x_3270_);
v___x_3281_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3270_, v___x_3275_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec_ref(v___x_3275_);
return v___x_3290_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3366_; 
v_cacheInferType_3366_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3366_ == 0)
{
goto v___jp_3144_;
}
else
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Lean_Expr_hasMVar(v_e_3123_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_inc_ref(v_e_3123_);
v___x_3368_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3433_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3433_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3433_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3413_; lean_object* v_cache_3414_; lean_object* v_inferType_3415_; lean_object* v___x_3416_; 
v___x_3413_ = lean_st_ref_get(v_a_3125_);
v_cache_3414_ = lean_ctor_get(v___x_3413_, 1);
lean_inc_ref(v_cache_3414_);
lean_dec(v___x_3413_);
v_inferType_3415_ = lean_ctor_get(v_cache_3414_, 0);
lean_inc_ref(v_inferType_3415_);
lean_dec_ref(v_cache_3414_);
v___x_3416_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3415_, v_a_3369_);
lean_dec_ref(v_inferType_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_cancelTk_x3f_3417_; 
lean_del_object(v___x_3371_);
v_cancelTk_x3f_3417_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3417_) == 1)
{
lean_object* v_val_3418_; uint8_t v___x_3419_; 
v_val_3418_ = lean_ctor_get(v_cancelTk_x3f_3417_, 0);
v___x_3419_ = l_IO_CancelToken_isSet(v_val_3418_);
if (v___x_3419_ == 0)
{
goto v___jp_3373_;
}
else
{
lean_object* v___x_3420_; lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_a_3369_);
lean_dec_ref_known(v_e_3123_, 3);
v___x_3420_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
goto v___jp_3373_;
}
}
else
{
lean_object* v_val_3429_; lean_object* v___x_3431_; 
lean_dec(v_a_3369_);
lean_dec_ref_known(v_e_3123_, 3);
v_val_3429_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_val_3429_);
lean_dec_ref_known(v___x_3416_, 1);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_val_3429_);
v___x_3431_ = v___x_3371_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_val_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
v___jp_3373_:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; uint8_t v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
v___x_3376_ = l_Lean_Expr_hasMVar(v_a_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3411_; 
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3374_, 0);
lean_dec(v_unused_3412_);
v___x_3378_ = v___x_3374_;
v_isShared_3379_ = v_isSharedCheck_3411_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v___x_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3411_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v_cache_3381_; lean_object* v_mctx_3382_; lean_object* v_zetaDeltaFVarIds_3383_; lean_object* v_postponed_3384_; lean_object* v_diag_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3410_; 
v___x_3380_ = lean_st_ref_take(v_a_3125_);
v_cache_3381_ = lean_ctor_get(v___x_3380_, 1);
v_mctx_3382_ = lean_ctor_get(v___x_3380_, 0);
v_zetaDeltaFVarIds_3383_ = lean_ctor_get(v___x_3380_, 2);
v_postponed_3384_ = lean_ctor_get(v___x_3380_, 3);
v_diag_3385_ = lean_ctor_get(v___x_3380_, 4);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3387_ = v___x_3380_;
v_isShared_3388_ = v_isSharedCheck_3410_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_diag_3385_);
lean_inc(v_postponed_3384_);
lean_inc(v_zetaDeltaFVarIds_3383_);
lean_inc(v_cache_3381_);
lean_inc(v_mctx_3382_);
lean_dec(v___x_3380_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3410_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_inferType_3389_; lean_object* v_funInfo_3390_; lean_object* v_synthInstance_3391_; lean_object* v_whnf_3392_; lean_object* v_defEqTrans_3393_; lean_object* v_defEqPerm_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3409_; 
v_inferType_3389_ = lean_ctor_get(v_cache_3381_, 0);
v_funInfo_3390_ = lean_ctor_get(v_cache_3381_, 1);
v_synthInstance_3391_ = lean_ctor_get(v_cache_3381_, 2);
v_whnf_3392_ = lean_ctor_get(v_cache_3381_, 3);
v_defEqTrans_3393_ = lean_ctor_get(v_cache_3381_, 4);
v_defEqPerm_3394_ = lean_ctor_get(v_cache_3381_, 5);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_cache_3381_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3396_ = v_cache_3381_;
v_isShared_3397_ = v_isSharedCheck_3409_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_defEqPerm_3394_);
lean_inc(v_defEqTrans_3393_);
lean_inc(v_whnf_3392_);
lean_inc(v_synthInstance_3391_);
lean_inc(v_funInfo_3390_);
lean_inc(v_inferType_3389_);
lean_dec(v_cache_3381_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3409_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_inc(v_a_3375_);
v___x_3398_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3389_, v_a_3369_, v_a_3375_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_funInfo_3390_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_synthInstance_3391_);
lean_ctor_set(v_reuseFailAlloc_3408_, 3, v_whnf_3392_);
lean_ctor_set(v_reuseFailAlloc_3408_, 4, v_defEqTrans_3393_);
lean_ctor_set(v_reuseFailAlloc_3408_, 5, v_defEqPerm_3394_);
v___x_3400_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3400_);
v___x_3402_ = v___x_3387_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_mctx_3382_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_zetaDeltaFVarIds_3383_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v_postponed_3384_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_diag_3385_);
v___x_3402_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_st_ref_set(v_a_3125_, v___x_3402_);
if (v_isShared_3379_ == 0)
{
v___x_3405_ = v___x_3378_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3375_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3375_);
lean_dec(v_a_3369_);
return v___x_3374_;
}
}
else
{
lean_dec(v_a_3369_);
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref_known(v_e_3123_, 3);
v_a_3434_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3368_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3368_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
goto v___jp_3144_;
}
}
}
case 9:
{
lean_object* v_a_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_a_3442_ = lean_ctor_get(v_e_3123_, 0);
lean_inc_ref(v_a_3442_);
lean_dec_ref_known(v_e_3123_, 1);
v___x_3443_ = l_Lean_Literal_type(v_a_3442_);
lean_dec_ref(v_a_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
case 10:
{
lean_object* v_expr_3445_; 
v_expr_3445_ = lean_ctor_get(v_e_3123_, 1);
lean_inc_ref(v_expr_3445_);
lean_dec_ref_known(v_e_3123_, 2);
v_e_3123_ = v_expr_3445_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3447_; lean_object* v_idx_3448_; lean_object* v_struct_3449_; uint8_t v_cacheInferType_3465_; 
v_typeName_3447_ = lean_ctor_get(v_e_3123_, 0);
lean_inc(v_typeName_3447_);
v_idx_3448_ = lean_ctor_get(v_e_3123_, 1);
lean_inc(v_idx_3448_);
v_struct_3449_ = lean_ctor_get(v_e_3123_, 2);
lean_inc_ref(v_struct_3449_);
v_cacheInferType_3465_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3465_ == 0)
{
lean_dec_ref_known(v_e_3123_, 3);
goto v___jp_3450_;
}
else
{
uint8_t v___x_3466_; 
v___x_3466_ = l_Lean_Expr_hasMVar(v_e_3123_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3532_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3532_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3532_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3512_; lean_object* v_cache_3513_; lean_object* v_inferType_3514_; lean_object* v___x_3515_; 
v___x_3512_ = lean_st_ref_get(v_a_3125_);
v_cache_3513_ = lean_ctor_get(v___x_3512_, 1);
lean_inc_ref(v_cache_3513_);
lean_dec(v___x_3512_);
v_inferType_3514_ = lean_ctor_get(v_cache_3513_, 0);
lean_inc_ref(v_inferType_3514_);
lean_dec_ref(v_cache_3513_);
v___x_3515_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3514_, v_a_3468_);
lean_dec_ref(v_inferType_3514_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_cancelTk_x3f_3516_; 
lean_del_object(v___x_3470_);
v_cancelTk_x3f_3516_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3516_) == 1)
{
lean_object* v_val_3517_; uint8_t v___x_3518_; 
v_val_3517_ = lean_ctor_get(v_cancelTk_x3f_3516_, 0);
v___x_3518_ = l_IO_CancelToken_isSet(v_val_3517_);
if (v___x_3518_ == 0)
{
goto v___jp_3472_;
}
else
{
lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_a_3468_);
lean_dec_ref(v_struct_3449_);
lean_dec(v_idx_3448_);
lean_dec(v_typeName_3447_);
v___x_3519_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
goto v___jp_3472_;
}
}
else
{
lean_object* v_val_3528_; lean_object* v___x_3530_; 
lean_dec(v_a_3468_);
lean_dec_ref(v_struct_3449_);
lean_dec(v_idx_3448_);
lean_dec(v_typeName_3447_);
v_val_3528_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_val_3528_);
lean_dec_ref_known(v___x_3515_, 1);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v_val_3528_);
v___x_3530_ = v___x_3470_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_val_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
v___jp_3472_:
{
lean_object* v___x_3473_; 
v___x_3473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3447_, v_idx_3448_, v_struct_3449_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; uint8_t v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
v___x_3475_ = l_Lean_Expr_hasMVar(v_a_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3510_; 
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3510_ == 0)
{
lean_object* v_unused_3511_; 
v_unused_3511_ = lean_ctor_get(v___x_3473_, 0);
lean_dec(v_unused_3511_);
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3510_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3510_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v_cache_3480_; lean_object* v_mctx_3481_; lean_object* v_zetaDeltaFVarIds_3482_; lean_object* v_postponed_3483_; lean_object* v_diag_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3509_; 
v___x_3479_ = lean_st_ref_take(v_a_3125_);
v_cache_3480_ = lean_ctor_get(v___x_3479_, 1);
v_mctx_3481_ = lean_ctor_get(v___x_3479_, 0);
v_zetaDeltaFVarIds_3482_ = lean_ctor_get(v___x_3479_, 2);
v_postponed_3483_ = lean_ctor_get(v___x_3479_, 3);
v_diag_3484_ = lean_ctor_get(v___x_3479_, 4);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3486_ = v___x_3479_;
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_diag_3484_);
lean_inc(v_postponed_3483_);
lean_inc(v_zetaDeltaFVarIds_3482_);
lean_inc(v_cache_3480_);
lean_inc(v_mctx_3481_);
lean_dec(v___x_3479_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v_inferType_3488_; lean_object* v_funInfo_3489_; lean_object* v_synthInstance_3490_; lean_object* v_whnf_3491_; lean_object* v_defEqTrans_3492_; lean_object* v_defEqPerm_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3508_; 
v_inferType_3488_ = lean_ctor_get(v_cache_3480_, 0);
v_funInfo_3489_ = lean_ctor_get(v_cache_3480_, 1);
v_synthInstance_3490_ = lean_ctor_get(v_cache_3480_, 2);
v_whnf_3491_ = lean_ctor_get(v_cache_3480_, 3);
v_defEqTrans_3492_ = lean_ctor_get(v_cache_3480_, 4);
v_defEqPerm_3493_ = lean_ctor_get(v_cache_3480_, 5);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_cache_3480_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3495_ = v_cache_3480_;
v_isShared_3496_ = v_isSharedCheck_3508_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_defEqPerm_3493_);
lean_inc(v_defEqTrans_3492_);
lean_inc(v_whnf_3491_);
lean_inc(v_synthInstance_3490_);
lean_inc(v_funInfo_3489_);
lean_inc(v_inferType_3488_);
lean_dec(v_cache_3480_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3508_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_inc(v_a_3474_);
v___x_3497_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3488_, v_a_3468_, v_a_3474_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3497_);
v___x_3499_ = v___x_3495_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_funInfo_3489_);
lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_synthInstance_3490_);
lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_whnf_3491_);
lean_ctor_set(v_reuseFailAlloc_3507_, 4, v_defEqTrans_3492_);
lean_ctor_set(v_reuseFailAlloc_3507_, 5, v_defEqPerm_3493_);
v___x_3499_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___x_3499_);
v___x_3501_ = v___x_3486_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_mctx_3481_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_zetaDeltaFVarIds_3482_);
lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_postponed_3483_);
lean_ctor_set(v_reuseFailAlloc_3506_, 4, v_diag_3484_);
v___x_3501_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_st_ref_set(v_a_3125_, v___x_3501_);
if (v_isShared_3478_ == 0)
{
v___x_3504_ = v___x_3477_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3474_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3474_);
lean_dec(v_a_3468_);
return v___x_3473_;
}
}
else
{
lean_dec(v_a_3468_);
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_struct_3449_);
lean_dec(v_idx_3448_);
lean_dec(v_typeName_3447_);
v_a_3533_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3467_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3467_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3123_, 3);
goto v___jp_3450_;
}
}
v___jp_3450_:
{
lean_object* v_cancelTk_x3f_3451_; 
v_cancelTk_x3f_3451_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3451_) == 1)
{
lean_object* v_val_3452_; uint8_t v___x_3453_; 
v_val_3452_ = lean_ctor_get(v_cancelTk_x3f_3451_, 0);
v___x_3453_ = l_IO_CancelToken_isSet(v_val_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3447_, v_idx_3448_, v_struct_3449_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3454_;
}
else
{
lean_object* v___x_3455_; lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v_struct_3449_);
lean_dec(v_idx_3448_);
lean_dec(v_typeName_3447_);
v___x_3455_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3447_, v_idx_3448_, v_struct_3449_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3464_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3541_; 
v_cacheInferType_3541_ = lean_ctor_get_uint8(v_a_3124_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3541_ == 0)
{
goto v___jp_3129_;
}
else
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Expr_hasMVar(v_e_3123_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_inc_ref(v_e_3123_);
v___x_3543_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3608_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3608_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3608_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3588_; lean_object* v_cache_3589_; lean_object* v_inferType_3590_; lean_object* v___x_3591_; 
v___x_3588_ = lean_st_ref_get(v_a_3125_);
v_cache_3589_ = lean_ctor_get(v___x_3588_, 1);
lean_inc_ref(v_cache_3589_);
lean_dec(v___x_3588_);
v_inferType_3590_ = lean_ctor_get(v_cache_3589_, 0);
lean_inc_ref(v_inferType_3590_);
lean_dec_ref(v_cache_3589_);
v___x_3591_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3590_, v_a_3544_);
lean_dec_ref(v_inferType_3590_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_cancelTk_x3f_3592_; 
lean_del_object(v___x_3546_);
v_cancelTk_x3f_3592_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3592_) == 1)
{
lean_object* v_val_3593_; uint8_t v___x_3594_; 
v_val_3593_ = lean_ctor_get(v_cancelTk_x3f_3592_, 0);
v___x_3594_ = l_IO_CancelToken_isSet(v_val_3593_);
if (v___x_3594_ == 0)
{
goto v___jp_3548_;
}
else
{
lean_object* v___x_3595_; lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3544_);
lean_dec_ref(v_e_3123_);
v___x_3595_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
goto v___jp_3548_;
}
}
else
{
lean_object* v_val_3604_; lean_object* v___x_3606_; 
lean_dec(v_a_3544_);
lean_dec_ref(v_e_3123_);
v_val_3604_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v___x_3591_, 1);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v_val_3604_);
v___x_3606_ = v___x_3546_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_val_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
v___jp_3548_:
{
lean_object* v___x_3549_; 
v___x_3549_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; uint8_t v___x_3551_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
v___x_3551_ = l_Lean_Expr_hasMVar(v_a_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v___x_3549_, 0);
lean_dec(v_unused_3587_);
v___x_3553_ = v___x_3549_;
v_isShared_3554_ = v_isSharedCheck_3586_;
goto v_resetjp_3552_;
}
else
{
lean_dec(v___x_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3586_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v_cache_3556_; lean_object* v_mctx_3557_; lean_object* v_zetaDeltaFVarIds_3558_; lean_object* v_postponed_3559_; lean_object* v_diag_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3585_; 
v___x_3555_ = lean_st_ref_take(v_a_3125_);
v_cache_3556_ = lean_ctor_get(v___x_3555_, 1);
v_mctx_3557_ = lean_ctor_get(v___x_3555_, 0);
v_zetaDeltaFVarIds_3558_ = lean_ctor_get(v___x_3555_, 2);
v_postponed_3559_ = lean_ctor_get(v___x_3555_, 3);
v_diag_3560_ = lean_ctor_get(v___x_3555_, 4);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3562_ = v___x_3555_;
v_isShared_3563_ = v_isSharedCheck_3585_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_diag_3560_);
lean_inc(v_postponed_3559_);
lean_inc(v_zetaDeltaFVarIds_3558_);
lean_inc(v_cache_3556_);
lean_inc(v_mctx_3557_);
lean_dec(v___x_3555_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3585_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_inferType_3564_; lean_object* v_funInfo_3565_; lean_object* v_synthInstance_3566_; lean_object* v_whnf_3567_; lean_object* v_defEqTrans_3568_; lean_object* v_defEqPerm_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3584_; 
v_inferType_3564_ = lean_ctor_get(v_cache_3556_, 0);
v_funInfo_3565_ = lean_ctor_get(v_cache_3556_, 1);
v_synthInstance_3566_ = lean_ctor_get(v_cache_3556_, 2);
v_whnf_3567_ = lean_ctor_get(v_cache_3556_, 3);
v_defEqTrans_3568_ = lean_ctor_get(v_cache_3556_, 4);
v_defEqPerm_3569_ = lean_ctor_get(v_cache_3556_, 5);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_cache_3556_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3571_ = v_cache_3556_;
v_isShared_3572_ = v_isSharedCheck_3584_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_defEqPerm_3569_);
lean_inc(v_defEqTrans_3568_);
lean_inc(v_whnf_3567_);
lean_inc(v_synthInstance_3566_);
lean_inc(v_funInfo_3565_);
lean_inc(v_inferType_3564_);
lean_dec(v_cache_3556_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3584_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
lean_inc(v_a_3550_);
v___x_3573_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3564_, v_a_3544_, v_a_3550_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3573_);
v___x_3575_ = v___x_3571_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_funInfo_3565_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_synthInstance_3566_);
lean_ctor_set(v_reuseFailAlloc_3583_, 3, v_whnf_3567_);
lean_ctor_set(v_reuseFailAlloc_3583_, 4, v_defEqTrans_3568_);
lean_ctor_set(v_reuseFailAlloc_3583_, 5, v_defEqPerm_3569_);
v___x_3575_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3577_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v___x_3575_);
v___x_3577_ = v___x_3562_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_mctx_3557_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v_zetaDeltaFVarIds_3558_);
lean_ctor_set(v_reuseFailAlloc_3582_, 3, v_postponed_3559_);
lean_ctor_set(v_reuseFailAlloc_3582_, 4, v_diag_3560_);
v___x_3577_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3578_ = lean_st_ref_set(v_a_3125_, v___x_3577_);
if (v_isShared_3554_ == 0)
{
v___x_3580_ = v___x_3553_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3550_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3550_);
lean_dec(v_a_3544_);
return v___x_3549_;
}
}
else
{
lean_dec(v_a_3544_);
return v___x_3549_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec_ref(v_e_3123_);
v_a_3609_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3543_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3543_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
goto v___jp_3129_;
}
}
}
}
v___jp_3129_:
{
lean_object* v_cancelTk_x3f_3130_; 
v_cancelTk_x3f_3130_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3130_) == 1)
{
lean_object* v_val_3131_; uint8_t v___x_3132_; 
v_val_3131_ = lean_ctor_get(v_cancelTk_x3f_3130_, 0);
v___x_3132_ = l_IO_CancelToken_isSet(v_val_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v_e_3123_);
v___x_3134_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3143_;
}
}
v___jp_3144_:
{
lean_object* v_cancelTk_x3f_3145_; 
v_cancelTk_x3f_3145_ = lean_ctor_get(v_a_3126_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3145_) == 1)
{
lean_object* v_val_3146_; uint8_t v___x_3147_; 
v_val_3146_ = lean_ctor_get(v_cancelTk_x3f_3145_, 0);
v___x_3147_ = l_IO_CancelToken_isSet(v_val_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_e_3123_);
v___x_3149_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v___x_3158_; 
v___x_3158_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3625_, v_x_3626_, v_x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3633_, v_x_3634_, v_x_3635_);
lean_dec_ref(v_x_3635_);
lean_dec_ref(v_x_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3637_, lean_object* v_x_3638_, size_t v_x_3639_, size_t v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3638_, v_x_3639_, v_x_3640_, v_x_3641_, v_x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
size_t v_x_4009__boxed_3650_; size_t v_x_4010__boxed_3651_; lean_object* v_res_3652_; 
v_x_4009__boxed_3650_ = lean_unbox_usize(v_x_3646_);
lean_dec(v_x_3646_);
v_x_4010__boxed_3651_ = lean_unbox_usize(v_x_3647_);
lean_dec(v_x_3647_);
v_res_3652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3644_, v_x_3645_, v_x_4009__boxed_3650_, v_x_4010__boxed_3651_, v_x_3648_, v_x_3649_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3653_, lean_object* v_x_3654_, size_t v_x_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3654_, v_x_3655_, v_x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3658_, lean_object* v_x_3659_, lean_object* v_x_3660_, lean_object* v_x_3661_){
_start:
{
size_t v_x_4026__boxed_3662_; lean_object* v_res_3663_; 
v_x_4026__boxed_3662_ = lean_unbox_usize(v_x_3660_);
lean_dec(v_x_3660_);
v_res_3663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3658_, v_x_3659_, v_x_4026__boxed_3662_, v_x_3661_);
lean_dec_ref(v_x_3661_);
lean_dec_ref(v_x_3659_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3664_, lean_object* v_n_3665_, lean_object* v_k_3666_, lean_object* v_v_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3665_, v_k_3666_, v_v_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3669_, size_t v_depth_3670_, lean_object* v_keys_3671_, lean_object* v_vals_3672_, lean_object* v_heq_3673_, lean_object* v_i_3674_, lean_object* v_entries_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3670_, v_keys_3671_, v_vals_3672_, v_i_3674_, v_entries_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3677_, lean_object* v_depth_3678_, lean_object* v_keys_3679_, lean_object* v_vals_3680_, lean_object* v_heq_3681_, lean_object* v_i_3682_, lean_object* v_entries_3683_){
_start:
{
size_t v_depth_boxed_3684_; lean_object* v_res_3685_; 
v_depth_boxed_3684_ = lean_unbox_usize(v_depth_3678_);
lean_dec(v_depth_3678_);
v_res_3685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3677_, v_depth_boxed_3684_, v_keys_3679_, v_vals_3680_, v_heq_3681_, v_i_3682_, v_entries_3683_);
lean_dec_ref(v_vals_3680_);
lean_dec_ref(v_keys_3679_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3686_, lean_object* v_keys_3687_, lean_object* v_vals_3688_, lean_object* v_heq_3689_, lean_object* v_i_3690_, lean_object* v_k_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3687_, v_vals_3688_, v_i_3690_, v_k_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3693_, lean_object* v_keys_3694_, lean_object* v_vals_3695_, lean_object* v_heq_3696_, lean_object* v_i_3697_, lean_object* v_k_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3693_, v_keys_3694_, v_vals_3695_, v_heq_3696_, v_i_3697_, v_k_3698_);
lean_dec_ref(v_k_3698_);
lean_dec_ref(v_vals_3695_);
lean_dec_ref(v_keys_3694_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v_x_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3701_, v_x_3702_, v_x_3703_, v_x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = l_Lean_maxRecDepthErrorMessage;
v___x_3712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3714_ = l_Lean_MessageData_ofFormat(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3716_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3717_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___x_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3718_){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_ref_3718_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3726_, lean_object* v_ref_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3727_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3734_, lean_object* v_ref_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3734_, v_ref_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; uint8_t v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; uint8_t v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v_fileName_3861_; lean_object* v_fileMap_3862_; lean_object* v_options_3863_; lean_object* v_currRecDepth_3864_; lean_object* v_maxRecDepth_3865_; lean_object* v_ref_3866_; lean_object* v_currNamespace_3867_; lean_object* v_openDecls_3868_; lean_object* v_initHeartbeats_3869_; lean_object* v_maxHeartbeats_3870_; lean_object* v_quotContext_3871_; lean_object* v_currMacroScope_3872_; uint8_t v_diag_3873_; lean_object* v_cancelTk_x3f_3874_; uint8_t v_suppressElabErrors_3875_; lean_object* v_inheritedTraceOptions_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3894_; 
v_fileName_3861_ = lean_ctor_get(v_a_3745_, 0);
v_fileMap_3862_ = lean_ctor_get(v_a_3745_, 1);
v_options_3863_ = lean_ctor_get(v_a_3745_, 2);
v_currRecDepth_3864_ = lean_ctor_get(v_a_3745_, 3);
v_maxRecDepth_3865_ = lean_ctor_get(v_a_3745_, 4);
v_ref_3866_ = lean_ctor_get(v_a_3745_, 5);
v_currNamespace_3867_ = lean_ctor_get(v_a_3745_, 6);
v_openDecls_3868_ = lean_ctor_get(v_a_3745_, 7);
v_initHeartbeats_3869_ = lean_ctor_get(v_a_3745_, 8);
v_maxHeartbeats_3870_ = lean_ctor_get(v_a_3745_, 9);
v_quotContext_3871_ = lean_ctor_get(v_a_3745_, 10);
v_currMacroScope_3872_ = lean_ctor_get(v_a_3745_, 11);
v_diag_3873_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*14);
v_cancelTk_x3f_3874_ = lean_ctor_get(v_a_3745_, 12);
v_suppressElabErrors_3875_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3876_ = lean_ctor_get(v_a_3745_, 13);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3878_ = v_a_3745_;
v_isShared_3879_ = v_isSharedCheck_3894_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_inheritedTraceOptions_3876_);
lean_inc(v_cancelTk_x3f_3874_);
lean_inc(v_currMacroScope_3872_);
lean_inc(v_quotContext_3871_);
lean_inc(v_maxHeartbeats_3870_);
lean_inc(v_initHeartbeats_3869_);
lean_inc(v_openDecls_3868_);
lean_inc(v_currNamespace_3867_);
lean_inc(v_ref_3866_);
lean_inc(v_maxRecDepth_3865_);
lean_inc(v_currRecDepth_3864_);
lean_inc(v_options_3863_);
lean_inc(v_fileMap_3862_);
lean_inc(v_fileName_3861_);
lean_dec(v_a_3745_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3894_;
goto v_resetjp_3877_;
}
v___jp_3748_:
{
lean_object* v___x_3761_; uint8_t v_foApprox_3762_; uint8_t v_ctxApprox_3763_; uint8_t v_quasiPatternApprox_3764_; uint8_t v_constApprox_3765_; uint8_t v_isDefEqStuckEx_3766_; uint8_t v_unificationHints_3767_; uint8_t v_proofIrrelevance_3768_; uint8_t v_assignSyntheticOpaque_3769_; uint8_t v_offsetCnstrs_3770_; uint8_t v_transparency_3771_; uint8_t v_univApprox_3772_; uint8_t v_zetaUnused_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3787_; 
v___x_3761_ = l_Lean_Meta_Context_config(v___y_3753_);
lean_dec_ref(v___y_3753_);
v_foApprox_3762_ = lean_ctor_get_uint8(v___x_3761_, 0);
v_ctxApprox_3763_ = lean_ctor_get_uint8(v___x_3761_, 1);
v_quasiPatternApprox_3764_ = lean_ctor_get_uint8(v___x_3761_, 2);
v_constApprox_3765_ = lean_ctor_get_uint8(v___x_3761_, 3);
v_isDefEqStuckEx_3766_ = lean_ctor_get_uint8(v___x_3761_, 4);
v_unificationHints_3767_ = lean_ctor_get_uint8(v___x_3761_, 5);
v_proofIrrelevance_3768_ = lean_ctor_get_uint8(v___x_3761_, 6);
v_assignSyntheticOpaque_3769_ = lean_ctor_get_uint8(v___x_3761_, 7);
v_offsetCnstrs_3770_ = lean_ctor_get_uint8(v___x_3761_, 8);
v_transparency_3771_ = lean_ctor_get_uint8(v___x_3761_, 9);
v_univApprox_3772_ = lean_ctor_get_uint8(v___x_3761_, 11);
v_zetaUnused_3773_ = lean_ctor_get_uint8(v___x_3761_, 17);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3775_ = v___x_3761_;
v_isShared_3776_ = v_isSharedCheck_3787_;
goto v_resetjp_3774_;
}
else
{
lean_dec(v___x_3761_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3787_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
uint8_t v___x_3777_; uint8_t v___x_3778_; uint8_t v___x_3779_; lean_object* v___x_3781_; 
v___x_3777_ = 1;
v___x_3778_ = 0;
v___x_3779_ = 2;
if (v_isShared_3776_ == 0)
{
v___x_3781_ = v___x_3775_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 0, v_foApprox_3762_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 1, v_ctxApprox_3763_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 2, v_quasiPatternApprox_3764_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 3, v_constApprox_3765_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 4, v_isDefEqStuckEx_3766_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 5, v_unificationHints_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 6, v_proofIrrelevance_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 7, v_assignSyntheticOpaque_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 8, v_offsetCnstrs_3770_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 9, v_transparency_3771_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 11, v_univApprox_3772_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, 17, v_zetaUnused_3773_);
v___x_3781_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
uint64_t v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
lean_ctor_set_uint8(v___x_3781_, 10, v___x_3778_);
lean_ctor_set_uint8(v___x_3781_, 12, v___x_3777_);
lean_ctor_set_uint8(v___x_3781_, 13, v___x_3777_);
lean_ctor_set_uint8(v___x_3781_, 14, v___x_3779_);
lean_ctor_set_uint8(v___x_3781_, 15, v___x_3777_);
lean_ctor_set_uint8(v___x_3781_, 16, v___x_3777_);
lean_ctor_set_uint8(v___x_3781_, 18, v___x_3777_);
v___x_3782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3781_);
v___x_3783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set_uint64(v___x_3783_, sizeof(void*)*1, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___y_3758_);
lean_ctor_set(v___x_3784_, 2, v___y_3757_);
lean_ctor_set(v___x_3784_, 3, v___y_3749_);
lean_ctor_set(v___x_3784_, 4, v___y_3751_);
lean_ctor_set(v___x_3784_, 5, v___y_3750_);
lean_ctor_set(v___x_3784_, 6, v___y_3760_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*7, v___y_3752_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*7 + 1, v___y_3756_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*7 + 2, v___y_3759_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*7 + 3, v___y_3755_);
v___x_3785_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3742_, v___x_3784_, v_a_3744_, v___y_3754_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v___y_3754_);
lean_dec(v_a_3744_);
lean_dec_ref_known(v___x_3784_, 7);
return v___x_3785_;
}
}
}
v___jp_3788_:
{
lean_object* v___x_3791_; uint8_t v_foApprox_3792_; uint8_t v_ctxApprox_3793_; uint8_t v_quasiPatternApprox_3794_; uint8_t v_constApprox_3795_; uint8_t v_isDefEqStuckEx_3796_; uint8_t v_unificationHints_3797_; uint8_t v_proofIrrelevance_3798_; uint8_t v_assignSyntheticOpaque_3799_; uint8_t v_offsetCnstrs_3800_; uint8_t v_etaStruct_3801_; uint8_t v_univApprox_3802_; uint8_t v_iota_3803_; uint8_t v_beta_3804_; uint8_t v_proj_3805_; uint8_t v_zeta_3806_; uint8_t v_zetaDelta_3807_; uint8_t v_zetaUnused_3808_; uint8_t v_zetaHave_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3860_; 
v___x_3791_ = l_Lean_Meta_Context_config(v_a_3743_);
v_foApprox_3792_ = lean_ctor_get_uint8(v___x_3791_, 0);
v_ctxApprox_3793_ = lean_ctor_get_uint8(v___x_3791_, 1);
v_quasiPatternApprox_3794_ = lean_ctor_get_uint8(v___x_3791_, 2);
v_constApprox_3795_ = lean_ctor_get_uint8(v___x_3791_, 3);
v_isDefEqStuckEx_3796_ = lean_ctor_get_uint8(v___x_3791_, 4);
v_unificationHints_3797_ = lean_ctor_get_uint8(v___x_3791_, 5);
v_proofIrrelevance_3798_ = lean_ctor_get_uint8(v___x_3791_, 6);
v_assignSyntheticOpaque_3799_ = lean_ctor_get_uint8(v___x_3791_, 7);
v_offsetCnstrs_3800_ = lean_ctor_get_uint8(v___x_3791_, 8);
v_etaStruct_3801_ = lean_ctor_get_uint8(v___x_3791_, 10);
v_univApprox_3802_ = lean_ctor_get_uint8(v___x_3791_, 11);
v_iota_3803_ = lean_ctor_get_uint8(v___x_3791_, 12);
v_beta_3804_ = lean_ctor_get_uint8(v___x_3791_, 13);
v_proj_3805_ = lean_ctor_get_uint8(v___x_3791_, 14);
v_zeta_3806_ = lean_ctor_get_uint8(v___x_3791_, 15);
v_zetaDelta_3807_ = lean_ctor_get_uint8(v___x_3791_, 16);
v_zetaUnused_3808_ = lean_ctor_get_uint8(v___x_3791_, 17);
v_zetaHave_3809_ = lean_ctor_get_uint8(v___x_3791_, 18);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3811_ = v___x_3791_;
v_isShared_3812_ = v_isSharedCheck_3860_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v___x_3791_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3860_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
uint8_t v_trackZetaDelta_3813_; lean_object* v_zetaDeltaSet_3814_; lean_object* v_lctx_3815_; lean_object* v_localInstances_3816_; lean_object* v_defEqCtx_x3f_3817_; lean_object* v_synthPendingDepth_3818_; lean_object* v_canUnfold_x3f_3819_; uint8_t v_univApprox_3820_; uint8_t v_inTypeClassResolution_3821_; uint8_t v_cacheInferType_3822_; lean_object* v_config_3824_; 
v_trackZetaDelta_3813_ = lean_ctor_get_uint8(v_a_3743_, sizeof(void*)*7);
v_zetaDeltaSet_3814_ = lean_ctor_get(v_a_3743_, 1);
lean_inc(v_zetaDeltaSet_3814_);
v_lctx_3815_ = lean_ctor_get(v_a_3743_, 2);
lean_inc_ref(v_lctx_3815_);
v_localInstances_3816_ = lean_ctor_get(v_a_3743_, 3);
lean_inc_ref(v_localInstances_3816_);
v_defEqCtx_x3f_3817_ = lean_ctor_get(v_a_3743_, 4);
lean_inc(v_defEqCtx_x3f_3817_);
v_synthPendingDepth_3818_ = lean_ctor_get(v_a_3743_, 5);
lean_inc(v_synthPendingDepth_3818_);
v_canUnfold_x3f_3819_ = lean_ctor_get(v_a_3743_, 6);
lean_inc(v_canUnfold_x3f_3819_);
v_univApprox_3820_ = lean_ctor_get_uint8(v_a_3743_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3821_ = lean_ctor_get_uint8(v_a_3743_, sizeof(void*)*7 + 2);
v_cacheInferType_3822_ = lean_ctor_get_uint8(v_a_3743_, sizeof(void*)*7 + 3);
if (v_isShared_3812_ == 0)
{
v_config_3824_ = v___x_3811_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 0, v_foApprox_3792_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 1, v_ctxApprox_3793_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 2, v_quasiPatternApprox_3794_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 3, v_constApprox_3795_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 4, v_isDefEqStuckEx_3796_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 5, v_unificationHints_3797_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 6, v_proofIrrelevance_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 7, v_assignSyntheticOpaque_3799_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 8, v_offsetCnstrs_3800_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 10, v_etaStruct_3801_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 11, v_univApprox_3802_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 12, v_iota_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 13, v_beta_3804_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 14, v_proj_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 15, v_zeta_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 16, v_zetaDelta_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 17, v_zetaUnused_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, 18, v_zetaHave_3809_);
v_config_3824_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
uint64_t v___x_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3851_; 
lean_ctor_set_uint8(v_config_3824_, 9, v___y_3790_);
v___x_3825_ = l_Lean_Meta_Context_configKey(v_a_3743_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; lean_object* v_unused_3858_; 
v_unused_3852_ = lean_ctor_get(v_a_3743_, 6);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_a_3743_, 5);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_a_3743_, 4);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_a_3743_, 3);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_a_3743_, 2);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_a_3743_, 1);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_a_3743_, 0);
lean_dec(v_unused_3858_);
v___x_3827_ = v_a_3743_;
v_isShared_3828_ = v_isSharedCheck_3851_;
goto v_resetjp_3826_;
}
else
{
lean_dec(v_a_3743_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3851_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
uint64_t v___x_3829_; uint64_t v___x_3830_; uint64_t v___x_3831_; uint64_t v___x_3832_; uint64_t v_key_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3829_ = 3ULL;
v___x_3830_ = lean_uint64_shift_right(v___x_3825_, v___x_3829_);
v___x_3831_ = lean_uint64_shift_left(v___x_3830_, v___x_3829_);
v___x_3832_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3790_);
v_key_3833_ = lean_uint64_lor(v___x_3831_, v___x_3832_);
v___x_3834_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3834_, 0, v_config_3824_);
lean_ctor_set_uint64(v___x_3834_, sizeof(void*)*1, v_key_3833_);
lean_inc(v_canUnfold_x3f_3819_);
lean_inc(v_synthPendingDepth_3818_);
lean_inc(v_defEqCtx_x3f_3817_);
lean_inc_ref(v_localInstances_3816_);
lean_inc_ref(v_lctx_3815_);
lean_inc(v_zetaDeltaSet_3814_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3834_);
v___x_3836_ = v___x_3827_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_zetaDeltaSet_3814_);
lean_ctor_set(v_reuseFailAlloc_3850_, 2, v_lctx_3815_);
lean_ctor_set(v_reuseFailAlloc_3850_, 3, v_localInstances_3816_);
lean_ctor_set(v_reuseFailAlloc_3850_, 4, v_defEqCtx_x3f_3817_);
lean_ctor_set(v_reuseFailAlloc_3850_, 5, v_synthPendingDepth_3818_);
lean_ctor_set(v_reuseFailAlloc_3850_, 6, v_canUnfold_x3f_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*7, v_trackZetaDelta_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*7 + 1, v_univApprox_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*7 + 3, v_cacheInferType_3822_);
v___x_3836_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; uint8_t v_beta_3838_; 
v___x_3837_ = l_Lean_Meta_Context_config(v___x_3836_);
v_beta_3838_ = lean_ctor_get_uint8(v___x_3837_, 13);
if (v_beta_3838_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v_iota_3839_; 
v_iota_3839_ = lean_ctor_get_uint8(v___x_3837_, 12);
if (v_iota_3839_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v_zeta_3840_; 
v_zeta_3840_ = lean_ctor_get_uint8(v___x_3837_, 15);
if (v_zeta_3840_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v_zetaHave_3841_; 
v_zetaHave_3841_ = lean_ctor_get_uint8(v___x_3837_, 18);
if (v_zetaHave_3841_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v_zetaDelta_3842_; 
v_zetaDelta_3842_ = lean_ctor_get_uint8(v___x_3837_, 16);
if (v_zetaDelta_3842_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v_etaStruct_3843_; uint8_t v_proj_3844_; uint8_t v___x_3845_; uint8_t v___x_3846_; 
v_etaStruct_3843_ = lean_ctor_get_uint8(v___x_3837_, 10);
v_proj_3844_ = lean_ctor_get_uint8(v___x_3837_, 14);
lean_dec_ref(v___x_3837_);
v___x_3845_ = 2;
v___x_3846_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
uint8_t v___x_3847_; uint8_t v___x_3848_; 
v___x_3847_ = 0;
v___x_3848_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3843_, v___x_3847_);
if (v___x_3848_ == 0)
{
v___y_3749_ = v_localInstances_3816_;
v___y_3750_ = v_synthPendingDepth_3818_;
v___y_3751_ = v_defEqCtx_x3f_3817_;
v___y_3752_ = v_trackZetaDelta_3813_;
v___y_3753_ = v___x_3836_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v_cacheInferType_3822_;
v___y_3756_ = v_univApprox_3820_;
v___y_3757_ = v_lctx_3815_;
v___y_3758_ = v_zetaDeltaSet_3814_;
v___y_3759_ = v_inTypeClassResolution_3821_;
v___y_3760_ = v_canUnfold_x3f_3819_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3849_; 
lean_dec(v_canUnfold_x3f_3819_);
lean_dec(v_synthPendingDepth_3818_);
lean_dec(v_defEqCtx_x3f_3817_);
lean_dec_ref(v_localInstances_3816_);
lean_dec_ref(v_lctx_3815_);
lean_dec(v_zetaDeltaSet_3814_);
v___x_3849_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3742_, v___x_3836_, v_a_3744_, v___y_3789_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v___y_3789_);
lean_dec(v_a_3744_);
lean_dec_ref(v___x_3836_);
return v___x_3849_;
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
}
}
v_resetjp_3877_:
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = lean_unsigned_to_nat(0u);
v___x_3891_ = lean_nat_dec_eq(v_maxRecDepth_3865_, v___x_3890_);
if (v___x_3891_ == 0)
{
uint8_t v___x_3892_; 
v___x_3892_ = lean_nat_dec_eq(v_currRecDepth_3864_, v_maxRecDepth_3865_);
if (v___x_3892_ == 0)
{
goto v___jp_3880_;
}
else
{
lean_object* v___x_3893_; 
lean_del_object(v___x_3878_);
lean_dec_ref(v_inheritedTraceOptions_3876_);
lean_dec(v_cancelTk_x3f_3874_);
lean_dec(v_currMacroScope_3872_);
lean_dec(v_quotContext_3871_);
lean_dec(v_maxHeartbeats_3870_);
lean_dec(v_initHeartbeats_3869_);
lean_dec(v_openDecls_3868_);
lean_dec(v_currNamespace_3867_);
lean_dec(v_maxRecDepth_3865_);
lean_dec(v_currRecDepth_3864_);
lean_dec_ref(v_options_3863_);
lean_dec_ref(v_fileMap_3862_);
lean_dec_ref(v_fileName_3861_);
lean_dec(v_a_3746_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec_ref(v_e_3742_);
v___x_3893_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3866_);
return v___x_3893_;
}
}
else
{
goto v___jp_3880_;
}
v___jp_3880_:
{
lean_object* v___x_3881_; uint8_t v_transparency_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3881_ = l_Lean_Meta_Context_config(v_a_3743_);
v_transparency_3882_ = lean_ctor_get_uint8(v___x_3881_, 9);
lean_dec_ref(v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(1u);
v___x_3884_ = lean_nat_add(v_currRecDepth_3864_, v___x_3883_);
lean_dec(v_currRecDepth_3864_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 3, v___x_3884_);
v___x_3886_ = v___x_3878_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_fileName_3861_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_fileMap_3862_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_options_3863_);
lean_ctor_set(v_reuseFailAlloc_3889_, 3, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3889_, 4, v_maxRecDepth_3865_);
lean_ctor_set(v_reuseFailAlloc_3889_, 5, v_ref_3866_);
lean_ctor_set(v_reuseFailAlloc_3889_, 6, v_currNamespace_3867_);
lean_ctor_set(v_reuseFailAlloc_3889_, 7, v_openDecls_3868_);
lean_ctor_set(v_reuseFailAlloc_3889_, 8, v_initHeartbeats_3869_);
lean_ctor_set(v_reuseFailAlloc_3889_, 9, v_maxHeartbeats_3870_);
lean_ctor_set(v_reuseFailAlloc_3889_, 10, v_quotContext_3871_);
lean_ctor_set(v_reuseFailAlloc_3889_, 11, v_currMacroScope_3872_);
lean_ctor_set(v_reuseFailAlloc_3889_, 12, v_cancelTk_x3f_3874_);
lean_ctor_set(v_reuseFailAlloc_3889_, 13, v_inheritedTraceOptions_3876_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*14, v_diag_3873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*14 + 1, v_suppressElabErrors_3875_);
v___x_3886_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
uint8_t v___x_3887_; uint8_t v___x_3888_; 
v___x_3887_ = 1;
v___x_3888_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3882_, v___x_3887_);
if (v___x_3888_ == 0)
{
v___y_3789_ = v___x_3886_;
v___y_3790_ = v_transparency_3882_;
goto v___jp_3788_;
}
else
{
v___y_3789_ = v___x_3886_;
v___y_3790_ = v___x_3887_;
goto v___jp_3788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = lean_infer_type(v_e_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v_res_3901_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3902_){
_start:
{
switch(lean_obj_tag(v_x_3902_))
{
case 0:
{
uint8_t v___x_3903_; 
v___x_3903_ = 1;
return v___x_3903_;
}
case 2:
{
lean_object* v_a_3904_; lean_object* v_a_3905_; uint8_t v___x_3906_; 
v_a_3904_ = lean_ctor_get(v_x_3902_, 0);
v_a_3905_ = lean_ctor_get(v_x_3902_, 1);
v___x_3906_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3904_);
if (v___x_3906_ == 0)
{
return v___x_3906_;
}
else
{
v_x_3902_ = v_a_3905_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3908_; 
v_a_3908_ = lean_ctor_get(v_x_3902_, 1);
v_x_3902_ = v_a_3908_;
goto _start;
}
default: 
{
uint8_t v___x_3910_; 
v___x_3910_ = 0;
return v___x_3910_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3911_){
_start:
{
uint8_t v_res_3912_; lean_object* v_r_3913_; 
v_res_3912_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3911_);
lean_dec(v_x_3911_);
v_r_3913_ = lean_box(v_res_3912_);
return v_r_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; lean_object* v_mctx_3918_; lean_object* v___x_3919_; lean_object* v_fst_3920_; lean_object* v_snd_3921_; lean_object* v___x_3922_; lean_object* v_cache_3923_; lean_object* v_zetaDeltaFVarIds_3924_; lean_object* v_postponed_3925_; lean_object* v_diag_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3935_; 
v___x_3917_ = lean_st_ref_get(v___y_3915_);
v_mctx_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc_ref(v_mctx_3918_);
lean_dec(v___x_3917_);
v___x_3919_ = lean_instantiate_level_mvars(v_mctx_3918_, v_l_3914_);
v_fst_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_fst_3920_);
v_snd_3921_ = lean_ctor_get(v___x_3919_, 1);
lean_inc(v_snd_3921_);
lean_dec_ref(v___x_3919_);
v___x_3922_ = lean_st_ref_take(v___y_3915_);
v_cache_3923_ = lean_ctor_get(v___x_3922_, 1);
v_zetaDeltaFVarIds_3924_ = lean_ctor_get(v___x_3922_, 2);
v_postponed_3925_ = lean_ctor_get(v___x_3922_, 3);
v_diag_3926_ = lean_ctor_get(v___x_3922_, 4);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v___x_3922_, 0);
lean_dec(v_unused_3936_);
v___x_3928_ = v___x_3922_;
v_isShared_3929_ = v_isSharedCheck_3935_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_diag_3926_);
lean_inc(v_postponed_3925_);
lean_inc(v_zetaDeltaFVarIds_3924_);
lean_inc(v_cache_3923_);
lean_dec(v___x_3922_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3935_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v_fst_3920_);
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_fst_3920_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_cache_3923_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_zetaDeltaFVarIds_3924_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_postponed_3925_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_diag_3926_);
v___x_3931_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_st_ref_set(v___y_3915_, v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_snd_3921_);
return v___x_3933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3937_, v___y_3938_);
lean_dec(v___y_3938_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3941_, v___y_3943_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3955_, lean_object* v_x_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
switch(lean_obj_tag(v_x_3955_))
{
case 3:
{
lean_object* v_u_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v_u_3966_ = lean_ctor_get(v_x_3955_, 0);
lean_inc(v_u_3966_);
lean_dec_ref_known(v_x_3955_, 1);
v___x_3967_ = lean_unsigned_to_nat(0u);
v___x_3968_ = lean_nat_dec_eq(v_x_3956_, v___x_3967_);
lean_dec(v_x_3956_);
if (v___x_3968_ == 0)
{
lean_dec(v_u_3966_);
goto v___jp_3962_;
}
else
{
lean_object* v___x_3969_; 
v___x_3969_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3966_, v_a_3958_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3980_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3980_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
uint8_t v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3974_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3970_);
lean_dec(v_a_3970_);
v___x_3975_ = l_Bool_toLBool(v___x_3974_);
v___x_3976_ = lean_box(v___x_3975_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3976_);
v___x_3978_ = v___x_3972_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3969_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3969_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3989_; lean_object* v_zero_3990_; uint8_t v_isZero_3991_; 
v_body_3989_ = lean_ctor_get(v_x_3955_, 2);
lean_inc_ref(v_body_3989_);
lean_dec_ref_known(v_x_3955_, 3);
v_zero_3990_ = lean_unsigned_to_nat(0u);
v_isZero_3991_ = lean_nat_dec_eq(v_x_3956_, v_zero_3990_);
if (v_isZero_3991_ == 1)
{
uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_body_3989_);
lean_dec(v_x_3956_);
v___x_3992_ = 0;
v___x_3993_ = lean_box(v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v_one_3995_; lean_object* v_n_3996_; 
v_one_3995_ = lean_unsigned_to_nat(1u);
v_n_3996_ = lean_nat_sub(v_x_3956_, v_one_3995_);
lean_dec(v_x_3956_);
v_x_3955_ = v_body_3989_;
v_x_3956_ = v_n_3996_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3998_; 
v_body_3998_ = lean_ctor_get(v_x_3955_, 3);
lean_inc_ref(v_body_3998_);
lean_dec_ref_known(v_x_3955_, 4);
v_x_3955_ = v_body_3998_;
goto _start;
}
case 10:
{
lean_object* v_expr_4000_; 
v_expr_4000_ = lean_ctor_get(v_x_3955_, 1);
lean_inc_ref(v_expr_4000_);
lean_dec_ref_known(v_x_3955_, 2);
v_x_3955_ = v_expr_4000_;
goto _start;
}
default: 
{
lean_dec(v_x_3956_);
lean_dec_ref(v_x_3955_);
goto v___jp_3962_;
}
}
v___jp_3962_:
{
uint8_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = 2;
v___x_3964_ = lean_box(v___x_3963_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_4002_, lean_object* v_x_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4002_, v_x_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_4010_, lean_object* v_x_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
switch(lean_obj_tag(v_x_4010_))
{
case 4:
{
lean_object* v_declName_4017_; lean_object* v_us_4018_; lean_object* v___x_4019_; 
v_declName_4017_ = lean_ctor_get(v_x_4010_, 0);
lean_inc(v_declName_4017_);
v_us_4018_ = lean_ctor_get(v_x_4010_, 1);
lean_inc(v_us_4018_);
lean_dec_ref_known(v_x_4010_, 2);
v___x_4019_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4017_, v_us_4018_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4021_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4020_, v_x_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v___x_4021_;
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v_x_4011_);
v_a_4022_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4019_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4019_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4030_; lean_object* v___x_4031_; 
v_fvarId_4030_ = lean_ctor_get(v_x_4010_, 0);
lean_inc(v_fvarId_4030_);
lean_dec_ref_known(v_x_4010_, 1);
v___x_4031_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4030_, v_a_4012_, v_a_4014_, v_a_4015_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4032_, v_x_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v___x_4033_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec(v_x_4011_);
v_a_4034_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4031_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4031_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4042_; lean_object* v___x_4043_; 
v_mvarId_4042_ = lean_ctor_get(v_x_4010_, 0);
lean_inc(v_mvarId_4042_);
lean_dec_ref_known(v_x_4010_, 1);
v___x_4043_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4042_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4044_, v_x_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v___x_4045_;
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_x_4011_);
v_a_4046_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4043_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4043_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
case 5:
{
lean_object* v_fn_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_fn_4054_ = lean_ctor_get(v_x_4010_, 0);
lean_inc_ref(v_fn_4054_);
lean_dec_ref_known(v_x_4010_, 2);
v___x_4055_ = lean_unsigned_to_nat(1u);
v___x_4056_ = lean_nat_add(v_x_4011_, v___x_4055_);
lean_dec(v_x_4011_);
v_x_4010_ = v_fn_4054_;
v_x_4011_ = v___x_4056_;
goto _start;
}
case 10:
{
lean_object* v_expr_4058_; 
v_expr_4058_ = lean_ctor_get(v_x_4010_, 1);
lean_inc_ref(v_expr_4058_);
lean_dec_ref_known(v_x_4010_, 2);
v_x_4010_ = v_expr_4058_;
goto _start;
}
case 8:
{
lean_object* v_body_4060_; 
v_body_4060_ = lean_ctor_get(v_x_4010_, 3);
lean_inc_ref(v_body_4060_);
lean_dec_ref_known(v_x_4010_, 4);
v_x_4010_ = v_body_4060_;
goto _start;
}
case 6:
{
lean_object* v_body_4062_; lean_object* v_zero_4063_; uint8_t v_isZero_4064_; 
v_body_4062_ = lean_ctor_get(v_x_4010_, 2);
lean_inc_ref(v_body_4062_);
lean_dec_ref_known(v_x_4010_, 3);
v_zero_4063_ = lean_unsigned_to_nat(0u);
v_isZero_4064_ = lean_nat_dec_eq(v_x_4011_, v_zero_4063_);
if (v_isZero_4064_ == 1)
{
uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
lean_dec_ref(v_body_4062_);
lean_dec(v_x_4011_);
v___x_4065_ = 0;
v___x_4066_ = lean_box(v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
else
{
lean_object* v_one_4068_; lean_object* v_n_4069_; 
v_one_4068_ = lean_unsigned_to_nat(1u);
v_n_4069_ = lean_nat_sub(v_x_4011_, v_one_4068_);
lean_dec(v_x_4011_);
v_x_4010_ = v_body_4062_;
v_x_4011_ = v_n_4069_;
goto _start;
}
}
default: 
{
uint8_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec(v_x_4011_);
lean_dec_ref(v_x_4010_);
v___x_4071_ = 2;
v___x_4072_ = lean_box(v___x_4071_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4074_, lean_object* v_x_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4074_, v_x_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
switch(lean_obj_tag(v_x_4082_))
{
case 0:
{
uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref_known(v_x_4082_, 1);
v___x_4088_ = 2;
v___x_4089_ = lean_box(v___x_4088_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
case 1:
{
lean_object* v_fvarId_4091_; lean_object* v___x_4092_; 
v_fvarId_4091_ = lean_ctor_get(v_x_4082_, 0);
lean_inc(v_fvarId_4091_);
lean_dec_ref_known(v_x_4082_, 1);
v___x_4092_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4091_, v_a_4083_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
v___x_4094_ = lean_unsigned_to_nat(0u);
v___x_4095_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4093_, v___x_4094_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4095_;
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
v_a_4096_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4092_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4092_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
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
case 2:
{
lean_object* v_mvarId_4104_; lean_object* v___x_4105_; 
v_mvarId_4104_ = lean_ctor_get(v_x_4082_, 0);
lean_inc(v_mvarId_4104_);
lean_dec_ref_known(v_x_4082_, 1);
v___x_4105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4104_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v___x_4107_ = lean_unsigned_to_nat(0u);
v___x_4108_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4106_, v___x_4107_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4108_;
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_a_4109_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4105_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4105_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
case 4:
{
lean_object* v_declName_4117_; lean_object* v_us_4118_; lean_object* v___x_4119_; 
v_declName_4117_ = lean_ctor_get(v_x_4082_, 0);
lean_inc(v_declName_4117_);
v_us_4118_ = lean_ctor_get(v_x_4082_, 1);
lean_inc(v_us_4118_);
lean_dec_ref_known(v_x_4082_, 2);
v___x_4119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4117_, v_us_4118_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4120_, v___x_4121_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4122_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
v_a_4123_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4119_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4119_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
case 5:
{
lean_object* v_fn_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_fn_4131_ = lean_ctor_get(v_x_4082_, 0);
lean_inc_ref(v_fn_4131_);
lean_dec_ref_known(v_x_4082_, 2);
v___x_4132_ = lean_unsigned_to_nat(1u);
v___x_4133_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4131_, v___x_4132_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4133_;
}
case 7:
{
lean_object* v_body_4134_; 
v_body_4134_ = lean_ctor_get(v_x_4082_, 2);
lean_inc_ref(v_body_4134_);
lean_dec_ref_known(v_x_4082_, 3);
v_x_4082_ = v_body_4134_;
goto _start;
}
case 8:
{
lean_object* v_body_4136_; 
v_body_4136_ = lean_ctor_get(v_x_4082_, 3);
lean_inc_ref(v_body_4136_);
lean_dec_ref_known(v_x_4082_, 4);
v_x_4082_ = v_body_4136_;
goto _start;
}
case 10:
{
lean_object* v_expr_4138_; 
v_expr_4138_ = lean_ctor_get(v_x_4082_, 1);
lean_inc_ref(v_expr_4138_);
lean_dec_ref_known(v_x_4082_, 2);
v_x_4082_ = v_expr_4138_;
goto _start;
}
case 11:
{
uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec_ref_known(v_x_4082_, 3);
v___x_4140_ = 2;
v___x_4141_ = lean_box(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
default: 
{
uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_dec_ref(v_x_4082_);
v___x_4143_ = 0;
v___x_4144_ = lean_box(v___x_4143_);
v___x_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
return v___x_4145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Meta_isPropQuick(v_x_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4159_; 
lean_inc_ref(v_e_4153_);
v___x_4159_ = l_Lean_Meta_isPropQuick(v_e_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4216_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4162_ = v___x_4159_;
v_isShared_4163_ = v_isSharedCheck_4216_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4216_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
uint8_t v___x_4164_; 
v___x_4164_ = lean_unbox(v_a_4160_);
lean_dec(v_a_4160_);
switch(v___x_4164_)
{
case 0:
{
uint8_t v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; 
lean_dec_ref(v_e_4153_);
v___x_4165_ = 0;
v___x_4166_ = lean_box(v___x_4165_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4166_);
v___x_4168_ = v___x_4162_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
case 1:
{
uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
lean_dec_ref(v_e_4153_);
v___x_4170_ = 1;
v___x_4171_ = lean_box(v___x_4170_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4171_);
v___x_4173_ = v___x_4162_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
default: 
{
lean_object* v___x_4175_; 
lean_del_object(v___x_4162_);
lean_inc(v_a_4157_);
lean_inc_ref(v_a_4156_);
lean_inc(v_a_4155_);
lean_inc_ref(v_a_4154_);
v___x_4175_ = lean_infer_type(v_e_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___x_4177_ = l_Lean_Meta_whnfD(v_a_4176_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4199_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4199_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4199_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
if (lean_obj_tag(v_a_4178_) == 3)
{
lean_object* v_u_4182_; lean_object* v___x_4183_; lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4193_; 
lean_del_object(v___x_4180_);
v_u_4182_ = lean_ctor_get(v_a_4178_, 0);
lean_inc(v_u_4182_);
lean_dec_ref_known(v_a_4178_, 1);
v___x_4183_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4182_, v_a_4155_);
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4193_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4193_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4188_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4184_);
lean_dec(v_a_4184_);
v___x_4189_ = lean_box(v___x_4188_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4189_);
v___x_4191_ = v___x_4186_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
else
{
uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
lean_dec(v_a_4178_);
v___x_4194_ = 0;
v___x_4195_ = lean_box(v___x_4194_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4195_);
v___x_4197_ = v___x_4180_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
v_a_4200_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4177_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4177_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v_a_4208_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4175_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4175_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v_e_4153_);
v_a_4217_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4159_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4159_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Meta_isProp(v_e_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4232_){
_start:
{
switch(lean_obj_tag(v_x_4232_))
{
case 0:
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_unsigned_to_nat(0u);
return v___x_4233_;
}
case 1:
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_unsigned_to_nat(1u);
return v___x_4234_;
}
case 2:
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_unsigned_to_nat(2u);
return v___x_4235_;
}
default: 
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_unsigned_to_nat(3u);
return v___x_4236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4237_);
lean_dec(v_x_4237_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4239_, lean_object* v_k_4240_){
_start:
{
if (lean_obj_tag(v_t_4239_) == 3)
{
lean_object* v_idx_4241_; lean_object* v___x_4242_; 
v_idx_4241_ = lean_ctor_get(v_t_4239_, 0);
lean_inc(v_idx_4241_);
lean_dec_ref_known(v_t_4239_, 1);
v___x_4242_ = lean_apply_1(v_k_4240_, v_idx_4241_);
return v___x_4242_;
}
else
{
lean_dec(v_t_4239_);
return v_k_4240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4243_, lean_object* v_ctorIdx_4244_, lean_object* v_t_4245_, lean_object* v_h_4246_, lean_object* v_k_4247_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4245_, v_k_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4249_, lean_object* v_ctorIdx_4250_, lean_object* v_t_4251_, lean_object* v_h_4252_, lean_object* v_k_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4249_, v_ctorIdx_4250_, v_t_4251_, v_h_4252_, v_k_4253_);
lean_dec(v_ctorIdx_4250_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4255_, lean_object* v_false_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4255_, v_false_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4258_, lean_object* v_t_4259_, lean_object* v_h_4260_, lean_object* v_false_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4259_, v_false_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4263_, lean_object* v_true_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4263_, v_true_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4266_, lean_object* v_t_4267_, lean_object* v_h_4268_, lean_object* v_true_4269_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4267_, v_true_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4271_, lean_object* v_undef_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4271_, v_undef_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4274_, lean_object* v_t_4275_, lean_object* v_h_4276_, lean_object* v_undef_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4275_, v_undef_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4279_, lean_object* v_bvar_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4279_, v_bvar_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4282_, lean_object* v_t_4283_, lean_object* v_h_4284_, lean_object* v_bvar_4285_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4283_, v_bvar_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4287_){
_start:
{
switch(v_x_4287_)
{
case 0:
{
lean_object* v___x_4288_; 
v___x_4288_ = lean_box(0);
return v___x_4288_;
}
case 1:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_box(1);
return v___x_4289_;
}
default: 
{
lean_object* v___x_4290_; 
v___x_4290_ = lean_box(2);
return v___x_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4291_){
_start:
{
uint8_t v_x_25__boxed_4292_; lean_object* v_res_4293_; 
v_x_25__boxed_4292_ = lean_unbox(v_x_4291_);
v_res_4293_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4294_){
_start:
{
switch(lean_obj_tag(v_x_4294_))
{
case 0:
{
uint8_t v___x_4295_; 
v___x_4295_ = 0;
return v___x_4295_;
}
case 1:
{
uint8_t v___x_4296_; 
v___x_4296_ = 1;
return v___x_4296_;
}
default: 
{
uint8_t v___x_4297_; 
v___x_4297_ = 2;
return v___x_4297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4298_){
_start:
{
uint8_t v_res_4299_; lean_object* v_r_4300_; 
v_res_4299_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4298_);
lean_dec(v_x_4298_);
v_r_4300_ = lean_box(v_res_4299_);
return v_r_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4302_){
_start:
{
switch(lean_obj_tag(v_e_4302_))
{
case 3:
{
lean_object* v_u_4303_; uint8_t v___x_4304_; 
v_u_4303_ = lean_ctor_get(v_e_4302_, 0);
v___x_4304_ = l_Lean_Level_isNeverZero(v_u_4303_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
v___x_4305_ = l_Lean_Level_isZero(v_u_4303_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_box(2);
return v___x_4306_;
}
else
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_box(1);
return v___x_4307_;
}
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_box(0);
return v___x_4308_;
}
}
case 5:
{
lean_object* v_fn_4309_; 
v_fn_4309_ = lean_ctor_get(v_e_4302_, 0);
if (lean_obj_tag(v_fn_4309_) == 4)
{
lean_object* v_declName_4310_; 
v_declName_4310_ = lean_ctor_get(v_fn_4309_, 0);
if (lean_obj_tag(v_declName_4310_) == 1)
{
lean_object* v_pre_4311_; 
v_pre_4311_ = lean_ctor_get(v_declName_4310_, 0);
if (lean_obj_tag(v_pre_4311_) == 0)
{
lean_object* v_arg_4312_; lean_object* v_str_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v_arg_4312_ = lean_ctor_get(v_e_4302_, 1);
v_str_4313_ = lean_ctor_get(v_declName_4310_, 1);
v___x_4314_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4315_ = lean_string_dec_eq(v_str_4313_, v___x_4314_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_box(2);
return v___x_4316_;
}
else
{
v_e_4302_ = v_arg_4312_;
goto _start;
}
}
else
{
lean_object* v___x_4318_; 
v___x_4318_ = lean_box(2);
return v___x_4318_;
}
}
else
{
lean_object* v___x_4319_; 
v___x_4319_ = lean_box(2);
return v___x_4319_;
}
}
else
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_box(2);
return v___x_4320_;
}
}
default: 
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_box(2);
return v___x_4321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4322_);
lean_dec_ref(v_e_4322_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4324_, lean_object* v_binderType_4325_){
_start:
{
if (lean_obj_tag(v_r_4324_) == 3)
{
lean_object* v_idx_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4338_; 
v_idx_4326_ = lean_ctor_get(v_r_4324_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_r_4324_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4328_ = v_r_4324_;
v_isShared_4329_ = v_isSharedCheck_4338_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_idx_4326_);
lean_dec(v_r_4324_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4338_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_zero_4330_; uint8_t v_isZero_4331_; 
v_zero_4330_ = lean_unsigned_to_nat(0u);
v_isZero_4331_ = lean_nat_dec_eq(v_idx_4326_, v_zero_4330_);
if (v_isZero_4331_ == 1)
{
lean_object* v___x_4332_; 
lean_del_object(v___x_4328_);
lean_dec(v_idx_4326_);
v___x_4332_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4325_);
return v___x_4332_;
}
else
{
lean_object* v_one_4333_; lean_object* v_n_4334_; lean_object* v___x_4336_; 
v_one_4333_ = lean_unsigned_to_nat(1u);
v_n_4334_ = lean_nat_sub(v_idx_4326_, v_one_4333_);
lean_dec(v_idx_4326_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v_n_4334_);
v___x_4336_ = v___x_4328_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_n_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
return v_r_4324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4339_, lean_object* v_binderType_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4339_, v_binderType_4340_);
lean_dec_ref(v_binderType_4340_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4342_, lean_object* v_x_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v_type_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; 
switch(lean_obj_tag(v_x_4342_))
{
case 7:
{
lean_object* v_binderType_4377_; lean_object* v_body_4378_; lean_object* v_zero_4379_; uint8_t v_isZero_4380_; 
v_binderType_4377_ = lean_ctor_get(v_x_4342_, 1);
v_body_4378_ = lean_ctor_get(v_x_4342_, 2);
v_zero_4379_ = lean_unsigned_to_nat(0u);
v_isZero_4380_ = lean_nat_dec_eq(v_x_4343_, v_zero_4379_);
if (v_isZero_4380_ == 1)
{
v_type_4350_ = v_x_4342_;
v___y_4351_ = v_a_4344_;
v___y_4352_ = v_a_4345_;
v___y_4353_ = v_a_4346_;
v___y_4354_ = v_a_4347_;
goto v___jp_4349_;
}
else
{
lean_object* v_one_4381_; lean_object* v_n_4382_; lean_object* v___x_4383_; 
lean_inc_ref(v_body_4378_);
lean_inc_ref(v_binderType_4377_);
lean_dec_ref_known(v_x_4342_, 3);
v_one_4381_ = lean_unsigned_to_nat(1u);
v_n_4382_ = lean_nat_sub(v_x_4343_, v_one_4381_);
v___x_4383_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4378_, v_n_4382_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_n_4382_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4392_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4386_ = v___x_4383_;
v_isShared_4387_ = v_isSharedCheck_4392_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4392_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4384_, v_binderType_4377_);
lean_dec_ref(v_binderType_4377_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 0, v___x_4388_);
v___x_4390_ = v___x_4386_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
else
{
lean_dec_ref(v_binderType_4377_);
return v___x_4383_;
}
}
}
case 8:
{
lean_object* v_type_4393_; lean_object* v_body_4394_; lean_object* v___x_4395_; 
v_type_4393_ = lean_ctor_get(v_x_4342_, 1);
lean_inc_ref(v_type_4393_);
v_body_4394_ = lean_ctor_get(v_x_4342_, 3);
lean_inc_ref(v_body_4394_);
lean_dec_ref_known(v_x_4342_, 4);
v___x_4395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4394_, v_x_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4404_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4404_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4404_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4400_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4396_, v_type_4393_);
lean_dec_ref(v_type_4393_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4400_);
v___x_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
lean_dec_ref(v_type_4393_);
return v___x_4395_;
}
}
case 10:
{
lean_object* v_expr_4405_; 
v_expr_4405_ = lean_ctor_get(v_x_4342_, 1);
lean_inc_ref(v_expr_4405_);
lean_dec_ref_known(v_x_4342_, 2);
v_x_4342_ = v_expr_4405_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4407_; lean_object* v___x_4408_; uint8_t v___x_4409_; 
v_deBruijnIndex_4407_ = lean_ctor_get(v_x_4342_, 0);
lean_inc(v_deBruijnIndex_4407_);
lean_dec_ref_known(v_x_4342_, 1);
v___x_4408_ = lean_unsigned_to_nat(0u);
v___x_4409_ = lean_nat_dec_eq(v_x_4343_, v___x_4408_);
if (v___x_4409_ == 0)
{
lean_dec(v_deBruijnIndex_4407_);
goto v___jp_4374_;
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_deBruijnIndex_4407_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
}
default: 
{
lean_object* v___x_4412_; uint8_t v___x_4413_; 
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = lean_nat_dec_eq(v_x_4343_, v___x_4412_);
if (v___x_4413_ == 0)
{
lean_dec_ref(v_x_4342_);
goto v___jp_4374_;
}
else
{
v_type_4350_ = v_x_4342_;
v___y_4351_ = v_a_4344_;
v___y_4352_ = v_a_4345_;
v___y_4353_ = v_a_4346_;
v___y_4354_ = v_a_4347_;
goto v___jp_4349_;
}
}
}
v___jp_4349_:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Lean_Meta_isPropQuick(v_type_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4365_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4365_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4365_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
uint8_t v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4360_ = lean_unbox(v_a_4356_);
lean_dec(v_a_4356_);
v___x_4361_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4360_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4361_);
v___x_4363_ = v___x_4358_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
v_a_4366_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4355_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4355_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
v___jp_4374_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = lean_box(2);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4414_, lean_object* v_x_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4414_, v_x_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_x_4415_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4422_, lean_object* v_n_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4422_, v_n_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4439_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4439_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4439_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4434_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4430_);
lean_dec(v_a_4430_);
v___x_4435_ = lean_box(v___x_4434_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4435_);
v___x_4437_ = v___x_4432_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
v_a_4440_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4429_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4429_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4448_, lean_object* v_n_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4448_, v_n_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
lean_dec(v_n_4449_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
switch(lean_obj_tag(v_x_4456_))
{
case 4:
{
lean_object* v_declName_4463_; lean_object* v_us_4464_; lean_object* v___x_4465_; 
v_declName_4463_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_declName_4463_);
v_us_4464_ = lean_ctor_get(v_x_4456_, 1);
lean_inc(v_us_4464_);
lean_dec_ref_known(v_x_4456_, 2);
v___x_4465_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4463_, v_us_4464_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4467_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4466_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4467_;
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_x_4457_);
v_a_4468_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4465_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4465_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4476_; lean_object* v___x_4477_; 
v_fvarId_4476_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_fvarId_4476_);
lean_dec_ref_known(v_x_4456_, 1);
v___x_4477_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4476_, v_a_4458_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v___x_4479_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4478_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4479_;
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec(v_x_4457_);
v_a_4480_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4477_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4477_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4488_; lean_object* v___x_4489_; 
v_mvarId_4488_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_mvarId_4488_);
lean_dec_ref_known(v_x_4456_, 1);
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4488_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4490_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_x_4457_);
v_a_4492_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4489_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4489_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
case 5:
{
lean_object* v_fn_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v_fn_4500_ = lean_ctor_get(v_x_4456_, 0);
lean_inc_ref(v_fn_4500_);
lean_dec_ref_known(v_x_4456_, 2);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = lean_nat_add(v_x_4457_, v___x_4501_);
lean_dec(v_x_4457_);
v_x_4456_ = v_fn_4500_;
v_x_4457_ = v___x_4502_;
goto _start;
}
case 10:
{
lean_object* v_expr_4504_; 
v_expr_4504_ = lean_ctor_get(v_x_4456_, 1);
lean_inc_ref(v_expr_4504_);
lean_dec_ref_known(v_x_4456_, 2);
v_x_4456_ = v_expr_4504_;
goto _start;
}
case 8:
{
lean_object* v_body_4506_; 
v_body_4506_ = lean_ctor_get(v_x_4456_, 3);
lean_inc_ref(v_body_4506_);
lean_dec_ref_known(v_x_4456_, 4);
v_x_4456_ = v_body_4506_;
goto _start;
}
case 6:
{
lean_object* v_body_4508_; lean_object* v_zero_4509_; uint8_t v_isZero_4510_; 
v_body_4508_ = lean_ctor_get(v_x_4456_, 2);
lean_inc_ref(v_body_4508_);
lean_dec_ref_known(v_x_4456_, 3);
v_zero_4509_ = lean_unsigned_to_nat(0u);
v_isZero_4510_ = lean_nat_dec_eq(v_x_4457_, v_zero_4509_);
if (v_isZero_4510_ == 1)
{
lean_object* v___x_4511_; 
lean_dec(v_x_4457_);
v___x_4511_ = l_Lean_Meta_isProofQuick(v_body_4508_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
return v___x_4511_;
}
else
{
lean_object* v_one_4512_; lean_object* v_n_4513_; 
v_one_4512_ = lean_unsigned_to_nat(1u);
v_n_4513_ = lean_nat_sub(v_x_4457_, v_one_4512_);
lean_dec(v_x_4457_);
v_x_4456_ = v_body_4508_;
v_x_4457_ = v_n_4513_;
goto _start;
}
}
default: 
{
uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec(v_x_4457_);
lean_dec_ref(v_x_4456_);
v___x_4515_ = 2;
v___x_4516_ = lean_box(v___x_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
switch(lean_obj_tag(v_x_4518_))
{
case 0:
{
uint8_t v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
lean_dec_ref_known(v_x_4518_, 1);
v___x_4524_ = 2;
v___x_4525_ = lean_box(v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
case 1:
{
lean_object* v_fvarId_4527_; lean_object* v___x_4528_; 
v_fvarId_4527_ = lean_ctor_get(v_x_4518_, 0);
lean_inc(v_fvarId_4527_);
lean_dec_ref_known(v_x_4518_, 1);
v___x_4528_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4527_, v_a_4519_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v___x_4528_, 1);
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4529_, v___x_4530_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4531_;
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
v_a_4532_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4528_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4528_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4540_; lean_object* v___x_4541_; 
v_mvarId_4540_ = lean_ctor_get(v_x_4518_, 0);
lean_inc(v_mvarId_4540_);
lean_dec_ref_known(v_x_4518_, 1);
v___x_4541_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4540_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4543_ = lean_unsigned_to_nat(0u);
v___x_4544_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4542_, v___x_4543_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4544_;
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
v_a_4545_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4541_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
case 4:
{
lean_object* v_declName_4553_; lean_object* v_us_4554_; lean_object* v___x_4555_; 
v_declName_4553_ = lean_ctor_get(v_x_4518_, 0);
lean_inc(v_declName_4553_);
v_us_4554_ = lean_ctor_get(v_x_4518_, 1);
lean_inc(v_us_4554_);
lean_dec_ref_known(v_x_4518_, 2);
v___x_4555_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4553_, v_us_4554_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref_known(v___x_4555_, 1);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4556_, v___x_4557_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4558_;
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
v_a_4559_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4555_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4555_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
case 5:
{
lean_object* v_fn_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_fn_4567_ = lean_ctor_get(v_x_4518_, 0);
lean_inc_ref(v_fn_4567_);
lean_dec_ref_known(v_x_4518_, 2);
v___x_4568_ = lean_unsigned_to_nat(1u);
v___x_4569_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4567_, v___x_4568_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4569_;
}
case 6:
{
lean_object* v_body_4570_; 
v_body_4570_ = lean_ctor_get(v_x_4518_, 2);
lean_inc_ref(v_body_4570_);
lean_dec_ref_known(v_x_4518_, 3);
v_x_4518_ = v_body_4570_;
goto _start;
}
case 8:
{
lean_object* v_body_4572_; 
v_body_4572_ = lean_ctor_get(v_x_4518_, 3);
lean_inc_ref(v_body_4572_);
lean_dec_ref_known(v_x_4518_, 4);
v_x_4518_ = v_body_4572_;
goto _start;
}
case 10:
{
lean_object* v_expr_4574_; 
v_expr_4574_ = lean_ctor_get(v_x_4518_, 1);
lean_inc_ref(v_expr_4574_);
lean_dec_ref_known(v_x_4518_, 2);
v_x_4518_ = v_expr_4574_;
goto _start;
}
case 11:
{
uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
lean_dec_ref_known(v_x_4518_, 3);
v___x_4576_ = 2;
v___x_4577_ = lean_box(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
default: 
{
uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
lean_dec_ref(v_x_4518_);
v___x_4579_ = 0;
v___x_4580_ = lean_box(v___x_4579_);
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_Meta_isProofQuick(v_x_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4589_, lean_object* v_x_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4589_, v_x_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; 
lean_inc_ref(v_e_4597_);
v___x_4603_ = l_Lean_Meta_isProofQuick(v_e_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4630_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4606_ = v___x_4603_;
v_isShared_4607_ = v_isSharedCheck_4630_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4603_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4630_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
uint8_t v___x_4608_; 
v___x_4608_ = lean_unbox(v_a_4604_);
lean_dec(v_a_4604_);
switch(v___x_4608_)
{
case 0:
{
uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_dec_ref(v_e_4597_);
v___x_4609_ = 0;
v___x_4610_ = lean_box(v___x_4609_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4610_);
v___x_4612_ = v___x_4606_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
case 1:
{
uint8_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4617_; 
lean_dec_ref(v_e_4597_);
v___x_4614_ = 1;
v___x_4615_ = lean_box(v___x_4614_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4615_);
v___x_4617_ = v___x_4606_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4615_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
default: 
{
lean_object* v___x_4619_; 
lean_del_object(v___x_4606_);
lean_inc(v_a_4601_);
lean_inc_ref(v_a_4600_);
lean_inc(v_a_4599_);
lean_inc_ref(v_a_4598_);
v___x_4619_ = lean_infer_type(v_e_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4621_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref_known(v___x_4619_, 1);
v___x_4621_ = l_Lean_Meta_isProp(v_a_4620_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
return v___x_4621_;
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
v_a_4622_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4619_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4619_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v_e_4597_);
v_a_4631_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4603_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4603_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lean_Meta_isProof(v_e_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4646_, lean_object* v_x_4647_){
_start:
{
switch(lean_obj_tag(v_x_4646_))
{
case 3:
{
lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4653_ = lean_unsigned_to_nat(0u);
v___x_4654_ = lean_nat_dec_eq(v_x_4647_, v___x_4653_);
lean_dec(v_x_4647_);
if (v___x_4654_ == 0)
{
goto v___jp_4649_;
}
else
{
uint8_t v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = 1;
v___x_4656_ = lean_box(v___x_4655_);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
case 7:
{
lean_object* v_body_4658_; lean_object* v_zero_4659_; uint8_t v_isZero_4660_; 
v_body_4658_ = lean_ctor_get(v_x_4646_, 2);
v_zero_4659_ = lean_unsigned_to_nat(0u);
v_isZero_4660_ = lean_nat_dec_eq(v_x_4647_, v_zero_4659_);
if (v_isZero_4660_ == 1)
{
uint8_t v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_dec(v_x_4647_);
v___x_4661_ = 0;
v___x_4662_ = lean_box(v___x_4661_);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
else
{
lean_object* v_one_4664_; lean_object* v_n_4665_; 
v_one_4664_ = lean_unsigned_to_nat(1u);
v_n_4665_ = lean_nat_sub(v_x_4647_, v_one_4664_);
lean_dec(v_x_4647_);
v_x_4646_ = v_body_4658_;
v_x_4647_ = v_n_4665_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4667_; 
v_body_4667_ = lean_ctor_get(v_x_4646_, 3);
v_x_4646_ = v_body_4667_;
goto _start;
}
case 10:
{
lean_object* v_expr_4669_; 
v_expr_4669_ = lean_ctor_get(v_x_4646_, 1);
v_x_4646_ = v_expr_4669_;
goto _start;
}
default: 
{
lean_dec(v_x_4647_);
goto v___jp_4649_;
}
}
v___jp_4649_:
{
uint8_t v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4650_ = 2;
v___x_4651_ = lean_box(v___x_4650_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
return v___x_4652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4671_, lean_object* v_x_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4671_, v_x_4672_);
lean_dec_ref(v_x_4671_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4675_, lean_object* v_x_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4675_, v_x_4676_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4683_, lean_object* v_x_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4683_, v_x_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec_ref(v_x_4683_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4691_, lean_object* v_x_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
switch(lean_obj_tag(v_x_4691_))
{
case 4:
{
lean_object* v_declName_4698_; lean_object* v_us_4699_; lean_object* v___x_4700_; 
v_declName_4698_ = lean_ctor_get(v_x_4691_, 0);
lean_inc(v_declName_4698_);
v_us_4699_ = lean_ctor_get(v_x_4691_, 1);
lean_inc(v_us_4699_);
lean_dec_ref_known(v_x_4691_, 2);
v___x_4700_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4698_, v_us_4699_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4702_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4702_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4701_, v_x_4692_);
lean_dec(v_a_4701_);
return v___x_4702_;
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_x_4692_);
v_a_4703_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4700_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4700_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4711_; lean_object* v___x_4712_; 
v_fvarId_4711_ = lean_ctor_get(v_x_4691_, 0);
lean_inc(v_fvarId_4711_);
lean_dec_ref_known(v_x_4691_, 1);
v___x_4712_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4711_, v_a_4693_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4714_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4713_);
lean_dec_ref_known(v___x_4712_, 1);
v___x_4714_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4713_, v_x_4692_);
lean_dec(v_a_4713_);
return v___x_4714_;
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec(v_x_4692_);
v_a_4715_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4712_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4712_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4723_; lean_object* v___x_4724_; 
v_mvarId_4723_ = lean_ctor_get(v_x_4691_, 0);
lean_inc(v_mvarId_4723_);
lean_dec_ref_known(v_x_4691_, 1);
v___x_4724_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4723_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4726_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___x_4724_, 1);
v___x_4726_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4725_, v_x_4692_);
lean_dec(v_a_4725_);
return v___x_4726_;
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec(v_x_4692_);
v_a_4727_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4724_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4724_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
case 5:
{
lean_object* v_fn_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v_fn_4735_ = lean_ctor_get(v_x_4691_, 0);
lean_inc_ref(v_fn_4735_);
lean_dec_ref_known(v_x_4691_, 2);
v___x_4736_ = lean_unsigned_to_nat(1u);
v___x_4737_ = lean_nat_add(v_x_4692_, v___x_4736_);
lean_dec(v_x_4692_);
v_x_4691_ = v_fn_4735_;
v_x_4692_ = v___x_4737_;
goto _start;
}
case 10:
{
lean_object* v_expr_4739_; 
v_expr_4739_ = lean_ctor_get(v_x_4691_, 1);
lean_inc_ref(v_expr_4739_);
lean_dec_ref_known(v_x_4691_, 2);
v_x_4691_ = v_expr_4739_;
goto _start;
}
case 8:
{
lean_object* v_body_4741_; 
v_body_4741_ = lean_ctor_get(v_x_4691_, 3);
lean_inc_ref(v_body_4741_);
lean_dec_ref_known(v_x_4691_, 4);
v_x_4691_ = v_body_4741_;
goto _start;
}
case 6:
{
lean_object* v_body_4743_; lean_object* v_zero_4744_; uint8_t v_isZero_4745_; 
v_body_4743_ = lean_ctor_get(v_x_4691_, 2);
lean_inc_ref(v_body_4743_);
lean_dec_ref_known(v_x_4691_, 3);
v_zero_4744_ = lean_unsigned_to_nat(0u);
v_isZero_4745_ = lean_nat_dec_eq(v_x_4692_, v_zero_4744_);
if (v_isZero_4745_ == 1)
{
uint8_t v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
lean_dec_ref(v_body_4743_);
lean_dec(v_x_4692_);
v___x_4746_ = 0;
v___x_4747_ = lean_box(v___x_4746_);
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
return v___x_4748_;
}
else
{
lean_object* v_one_4749_; lean_object* v_n_4750_; 
v_one_4749_ = lean_unsigned_to_nat(1u);
v_n_4750_ = lean_nat_sub(v_x_4692_, v_one_4749_);
lean_dec(v_x_4692_);
v_x_4691_ = v_body_4743_;
v_x_4692_ = v_n_4750_;
goto _start;
}
}
default: 
{
uint8_t v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
lean_dec(v_x_4692_);
lean_dec_ref(v_x_4691_);
v___x_4752_ = 2;
v___x_4753_ = lean_box(v___x_4752_);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4755_, lean_object* v_x_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4755_, v_x_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
switch(lean_obj_tag(v_x_4763_))
{
case 1:
{
lean_object* v_fvarId_4769_; lean_object* v___x_4770_; 
v_fvarId_4769_ = lean_ctor_get(v_x_4763_, 0);
lean_inc(v_fvarId_4769_);
lean_dec_ref_known(v_x_4763_, 1);
v___x_4770_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4769_, v_a_4764_, v_a_4766_, v_a_4767_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4770_, 1);
v___x_4772_ = lean_unsigned_to_nat(0u);
v___x_4773_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4771_, v___x_4772_);
lean_dec(v_a_4771_);
return v___x_4773_;
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
v_a_4774_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4770_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4770_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
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
case 2:
{
lean_object* v_mvarId_4782_; lean_object* v___x_4783_; 
v_mvarId_4782_ = lean_ctor_get(v_x_4763_, 0);
lean_inc(v_mvarId_4782_);
lean_dec_ref_known(v_x_4763_, 1);
v___x_4783_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4782_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
v___x_4785_ = lean_unsigned_to_nat(0u);
v___x_4786_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4784_, v___x_4785_);
lean_dec(v_a_4784_);
return v___x_4786_;
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
v_a_4787_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4783_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4783_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
case 3:
{
uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_dec_ref_known(v_x_4763_, 1);
v___x_4795_ = 1;
v___x_4796_ = lean_box(v___x_4795_);
v___x_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
return v___x_4797_;
}
case 4:
{
lean_object* v_declName_4798_; lean_object* v_us_4799_; lean_object* v___x_4800_; 
v_declName_4798_ = lean_ctor_get(v_x_4763_, 0);
lean_inc(v_declName_4798_);
v_us_4799_ = lean_ctor_get(v_x_4763_, 1);
lean_inc(v_us_4799_);
lean_dec_ref_known(v_x_4763_, 2);
v___x_4800_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4798_, v_us_4799_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc(v_a_4801_);
lean_dec_ref_known(v___x_4800_, 1);
v___x_4802_ = lean_unsigned_to_nat(0u);
v___x_4803_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4801_, v___x_4802_);
lean_dec(v_a_4801_);
return v___x_4803_;
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
v_a_4804_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4800_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4800_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
case 5:
{
lean_object* v_fn_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_fn_4812_ = lean_ctor_get(v_x_4763_, 0);
lean_inc_ref(v_fn_4812_);
lean_dec_ref_known(v_x_4763_, 2);
v___x_4813_ = lean_unsigned_to_nat(1u);
v___x_4814_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4812_, v___x_4813_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
return v___x_4814_;
}
case 6:
{
uint8_t v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_dec_ref_known(v_x_4763_, 3);
v___x_4815_ = 0;
v___x_4816_ = lean_box(v___x_4815_);
v___x_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
return v___x_4817_;
}
case 7:
{
uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
lean_dec_ref_known(v_x_4763_, 3);
v___x_4818_ = 1;
v___x_4819_ = lean_box(v___x_4818_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
return v___x_4820_;
}
case 8:
{
lean_object* v_body_4821_; 
v_body_4821_ = lean_ctor_get(v_x_4763_, 3);
lean_inc_ref(v_body_4821_);
lean_dec_ref_known(v_x_4763_, 4);
v_x_4763_ = v_body_4821_;
goto _start;
}
case 9:
{
uint8_t v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec_ref_known(v_x_4763_, 1);
v___x_4823_ = 0;
v___x_4824_ = lean_box(v___x_4823_);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
case 10:
{
lean_object* v_expr_4826_; 
v_expr_4826_ = lean_ctor_get(v_x_4763_, 1);
lean_inc_ref(v_expr_4826_);
lean_dec_ref_known(v_x_4763_, 2);
v_x_4763_ = v_expr_4826_;
goto _start;
}
default: 
{
uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
lean_dec_ref(v_x_4763_);
v___x_4828_ = 2;
v___x_4829_ = lean_box(v___x_4828_);
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4829_);
return v___x_4830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Meta_isTypeQuick(v_x_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; 
lean_inc_ref(v_e_4838_);
v___x_4844_ = l_Lean_Meta_isTypeQuick(v_e_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4894_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4894_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4894_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
uint8_t v___x_4849_; 
v___x_4849_ = lean_unbox(v_a_4845_);
lean_dec(v_a_4845_);
switch(v___x_4849_)
{
case 0:
{
uint8_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
lean_dec_ref(v_e_4838_);
v___x_4850_ = 0;
v___x_4851_ = lean_box(v___x_4850_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4851_);
v___x_4853_ = v___x_4847_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
case 1:
{
uint8_t v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
lean_dec_ref(v_e_4838_);
v___x_4855_ = 1;
v___x_4856_ = lean_box(v___x_4855_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4856_);
v___x_4858_ = v___x_4847_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
default: 
{
lean_object* v___x_4860_; 
lean_del_object(v___x_4847_);
lean_inc(v_a_4842_);
lean_inc_ref(v_a_4841_);
lean_inc(v_a_4840_);
lean_inc_ref(v_a_4839_);
v___x_4860_ = lean_infer_type(v_e_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = l_Lean_Meta_whnfD(v_a_4861_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4877_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4865_ = v___x_4862_;
v_isShared_4866_ = v_isSharedCheck_4877_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4862_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4877_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
if (lean_obj_tag(v_a_4863_) == 3)
{
uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
lean_dec_ref_known(v_a_4863_, 1);
v___x_4867_ = 1;
v___x_4868_ = lean_box(v___x_4867_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 0, v___x_4868_);
v___x_4870_ = v___x_4865_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
else
{
uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
lean_dec(v_a_4863_);
v___x_4872_ = 0;
v___x_4873_ = lean_box(v___x_4872_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 0, v___x_4873_);
v___x_4875_ = v___x_4865_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
v_a_4878_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4862_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4862_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_a_4886_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4860_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4860_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec_ref(v_e_4838_);
v_a_4895_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4844_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4844_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Meta_isType(v_e_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4910_){
_start:
{
switch(lean_obj_tag(v_x_4910_))
{
case 7:
{
lean_object* v_body_4911_; 
v_body_4911_ = lean_ctor_get(v_x_4910_, 2);
v_x_4910_ = v_body_4911_;
goto _start;
}
case 3:
{
lean_object* v_u_4913_; lean_object* v___x_4914_; 
v_u_4913_ = lean_ctor_get(v_x_4910_, 0);
lean_inc(v_u_4913_);
v___x_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_u_4913_);
return v___x_4914_;
}
default: 
{
lean_object* v___x_4915_; 
v___x_4915_ = lean_box(0);
return v___x_4915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4916_);
lean_dec_ref(v_x_4916_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4918_, lean_object* v_body_4919_, lean_object* v_x_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4918_, v_body_4919_, v_x_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4929_, lean_object* v_xs_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
switch(lean_obj_tag(v_type_4929_))
{
case 3:
{
lean_object* v_u_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
lean_dec_ref(v_xs_4930_);
v_u_4936_ = lean_ctor_get(v_type_4929_, 0);
lean_inc(v_u_4936_);
lean_dec_ref_known(v_type_4929_, 1);
v___x_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4937_, 0, v_u_4936_);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
return v___x_4938_;
}
case 7:
{
lean_object* v_binderName_4939_; lean_object* v_binderType_4940_; lean_object* v_body_4941_; uint8_t v_binderInfo_4942_; lean_object* v___f_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v_binderName_4939_ = lean_ctor_get(v_type_4929_, 0);
lean_inc(v_binderName_4939_);
v_binderType_4940_ = lean_ctor_get(v_type_4929_, 1);
lean_inc_ref(v_binderType_4940_);
v_body_4941_ = lean_ctor_get(v_type_4929_, 2);
lean_inc_ref(v_body_4941_);
v_binderInfo_4942_ = lean_ctor_get_uint8(v_type_4929_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4929_, 3);
lean_inc_ref(v_xs_4930_);
v___f_4943_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4943_, 0, v_xs_4930_);
lean_closure_set(v___f_4943_, 1, v_body_4941_);
v___x_4944_ = lean_expr_instantiate_rev(v_binderType_4940_, v_xs_4930_);
lean_dec_ref(v_xs_4930_);
lean_dec_ref(v_binderType_4940_);
v___x_4945_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4939_, v_binderInfo_4942_, v___x_4944_, v___f_4943_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4945_;
}
default: 
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_expr_instantiate_rev(v_type_4929_, v_xs_4930_);
lean_dec_ref(v_xs_4930_);
lean_dec_ref(v_type_4929_);
v___x_4947_ = l_Lean_Meta_whnfD(v___x_4946_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4963_; 
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_4963_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4963_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
switch(lean_obj_tag(v_a_4948_))
{
case 3:
{
lean_object* v_u_4952_; lean_object* v___x_4953_; lean_object* v___x_4955_; 
v_u_4952_ = lean_ctor_get(v_a_4948_, 0);
lean_inc(v_u_4952_);
lean_dec_ref_known(v_a_4948_, 1);
v___x_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_u_4952_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 0, v___x_4953_);
v___x_4955_ = v___x_4950_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4953_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
case 7:
{
lean_object* v___x_4957_; 
lean_del_object(v___x_4950_);
v___x_4957_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4929_ = v_a_4948_;
v_xs_4930_ = v___x_4957_;
goto _start;
}
default: 
{
lean_object* v___x_4959_; lean_object* v___x_4961_; 
lean_dec(v_a_4948_);
v___x_4959_ = lean_box(0);
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 0, v___x_4959_);
v___x_4961_ = v___x_4950_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4959_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
v_a_4964_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4947_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4947_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4972_, lean_object* v_body_4973_, lean_object* v_x_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = lean_array_push(v_xs_4972_, v_x_4974_);
v___x_4981_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4973_, v___x_4980_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4982_, lean_object* v_xs_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4982_, v_xs_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
lean_dec(v_a_4985_);
lean_dec_ref(v_a_4984_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4990_, lean_object* v_cache_4991_, lean_object* v_a_x3f_4992_){
_start:
{
lean_object* v___x_4994_; lean_object* v_mctx_4995_; lean_object* v_zetaDeltaFVarIds_4996_; lean_object* v_postponed_4997_; lean_object* v_diag_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5008_; 
v___x_4994_ = lean_st_ref_take(v_a_4990_);
v_mctx_4995_ = lean_ctor_get(v___x_4994_, 0);
v_zetaDeltaFVarIds_4996_ = lean_ctor_get(v___x_4994_, 2);
v_postponed_4997_ = lean_ctor_get(v___x_4994_, 3);
v_diag_4998_ = lean_ctor_get(v___x_4994_, 4);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5008_ == 0)
{
lean_object* v_unused_5009_; 
v_unused_5009_ = lean_ctor_get(v___x_4994_, 1);
lean_dec(v_unused_5009_);
v___x_5000_ = v___x_4994_;
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_diag_4998_);
lean_inc(v_postponed_4997_);
lean_inc(v_zetaDeltaFVarIds_4996_);
lean_inc(v_mctx_4995_);
lean_dec(v___x_4994_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 1, v_cache_4991_);
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_mctx_4995_);
lean_ctor_set(v_reuseFailAlloc_5007_, 1, v_cache_4991_);
lean_ctor_set(v_reuseFailAlloc_5007_, 2, v_zetaDeltaFVarIds_4996_);
lean_ctor_set(v_reuseFailAlloc_5007_, 3, v_postponed_4997_);
lean_ctor_set(v_reuseFailAlloc_5007_, 4, v_diag_4998_);
v___x_5003_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = lean_st_ref_set(v_a_4990_, v___x_5003_);
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5010_, lean_object* v_cache_5011_, lean_object* v_a_x3f_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5010_, v_cache_5011_, v_a_x3f_5012_);
lean_dec(v_a_x3f_5012_);
lean_dec(v_a_5010_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5015_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v___x_5022_; lean_object* v_cache_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5022_ = lean_st_ref_get(v_a_5017_);
v_cache_5023_ = lean_ctor_get(v___x_5022_, 1);
lean_inc_ref(v_cache_5023_);
lean_dec(v___x_5022_);
v___x_5024_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5015_, v___x_5024_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5042_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5028_ = v___x_5025_;
v_isShared_5029_ = v_isSharedCheck_5042_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5025_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5042_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
lean_inc(v_a_5026_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set_tag(v___x_5028_, 1);
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
v___x_5032_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5017_, v_cache_5023_, v___x_5031_);
lean_dec_ref(v___x_5031_);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5039_ == 0)
{
lean_object* v_unused_5040_; 
v_unused_5040_ = lean_ctor_get(v___x_5032_, 0);
lean_dec(v_unused_5040_);
v___x_5034_ = v___x_5032_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_dec(v___x_5032_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v_a_5026_);
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5026_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
v_a_5043_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5025_, 1);
v___x_5044_ = lean_box(0);
v___x_5045_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5017_, v_cache_5023_, v___x_5044_);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5052_ == 0)
{
lean_object* v_unused_5053_; 
v_unused_5053_ = lean_ctor_get(v___x_5045_, 0);
lean_dec(v_unused_5053_);
v___x_5047_ = v___x_5045_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_dec(v___x_5045_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set_tag(v___x_5047_, 1);
lean_ctor_set(v___x_5047_, 0, v_a_5043_);
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5043_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
else
{
lean_object* v___x_5054_; 
lean_dec_ref(v_type_5015_);
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5021_);
return v___x_5054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5083_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5071_ = v___x_5068_;
v_isShared_5072_ = v_isSharedCheck_5083_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5083_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
if (lean_obj_tag(v_a_5069_) == 0)
{
uint8_t v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5073_ = 0;
v___x_5074_ = lean_box(v___x_5073_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v___x_5074_);
v___x_5076_ = v___x_5071_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
else
{
uint8_t v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5081_; 
lean_dec_ref_known(v_a_5069_, 1);
v___x_5078_ = 1;
v___x_5079_ = lean_box(v___x_5078_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v___x_5079_);
v___x_5081_ = v___x_5071_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
v_a_5084_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5086_ = v___x_5068_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5068_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_Meta_isTypeFormerType(v_type_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5095_);
lean_dec(v_a_5094_);
lean_dec_ref(v_a_5093_);
return v_res_5098_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5099_, lean_object* v_x_5100_){
_start:
{
if (lean_obj_tag(v_x_5099_) == 0)
{
if (lean_obj_tag(v_x_5100_) == 0)
{
uint8_t v___x_5101_; 
v___x_5101_ = 1;
return v___x_5101_;
}
else
{
uint8_t v___x_5102_; 
v___x_5102_ = 0;
return v___x_5102_;
}
}
else
{
if (lean_obj_tag(v_x_5100_) == 0)
{
uint8_t v___x_5103_; 
v___x_5103_ = 0;
return v___x_5103_;
}
else
{
lean_object* v_val_5104_; lean_object* v_val_5105_; uint8_t v___x_5106_; 
v_val_5104_ = lean_ctor_get(v_x_5099_, 0);
v_val_5105_ = lean_ctor_get(v_x_5100_, 0);
v___x_5106_ = lean_level_eq(v_val_5104_, v_val_5105_);
return v___x_5106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5107_, lean_object* v_x_5108_){
_start:
{
uint8_t v_res_5109_; lean_object* v_r_5110_; 
v_res_5109_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5107_, v_x_5108_);
lean_dec(v_x_5108_);
lean_dec(v_x_5107_);
v_r_5110_ = lean_box(v_res_5109_);
return v_r_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5130_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5122_ = v___x_5119_;
v_isShared_5123_ = v_isSharedCheck_5130_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5119_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5130_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5124_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5125_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5120_, v___x_5124_);
lean_dec(v_a_5120_);
v___x_5126_ = lean_box(v___x_5125_);
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 0, v___x_5126_);
v___x_5128_ = v___x_5122_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
else
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5138_; 
v_a_5131_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5133_ = v___x_5119_;
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_5119_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5136_; 
if (v_isShared_5134_ == 0)
{
v___x_5136_ = v___x_5133_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Lean_Meta_isPropFormerType(v_type_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec_ref(v_a_5140_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v___x_5152_; 
lean_inc(v_a_5150_);
lean_inc_ref(v_a_5149_);
lean_inc(v_a_5148_);
lean_inc_ref(v_a_5147_);
v___x_5152_ = lean_infer_type(v_e_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_a_5153_; lean_object* v___x_5154_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref_known(v___x_5152_, 1);
v___x_5154_ = l_Lean_Meta_isTypeFormerType(v_a_5153_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
return v___x_5154_;
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
v_a_5155_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5152_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5152_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_Meta_isTypeFormer(v_e_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5170_, lean_object* v_maxFVars_x3f_5171_, lean_object* v_k_5172_, uint8_t v_cleanupAnnotations_5173_, uint8_t v_whnfType_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v___f_5180_; lean_object* v___x_5181_; 
v___f_5180_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5180_, 0, v_k_5172_);
v___x_5181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5170_, v_maxFVars_x3f_5171_, v___f_5180_, v_cleanupAnnotations_5173_, v_whnfType_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5181_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5181_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
v_a_5190_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5181_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5181_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5198_, lean_object* v_maxFVars_x3f_5199_, lean_object* v_k_5200_, lean_object* v_cleanupAnnotations_5201_, lean_object* v_whnfType_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5208_; uint8_t v_whnfType_boxed_5209_; lean_object* v_res_5210_; 
v_cleanupAnnotations_boxed_5208_ = lean_unbox(v_cleanupAnnotations_5201_);
v_whnfType_boxed_5209_ = lean_unbox(v_whnfType_5202_);
v_res_5210_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5198_, v_maxFVars_x3f_5199_, v_k_5200_, v_cleanupAnnotations_boxed_5208_, v_whnfType_boxed_5209_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5211_, lean_object* v_type_5212_, lean_object* v_maxFVars_x3f_5213_, lean_object* v_k_5214_, uint8_t v_cleanupAnnotations_5215_, uint8_t v_whnfType_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v___x_5222_; 
v___x_5222_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5212_, v_maxFVars_x3f_5213_, v_k_5214_, v_cleanupAnnotations_5215_, v_whnfType_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5223_, lean_object* v_type_5224_, lean_object* v_maxFVars_x3f_5225_, lean_object* v_k_5226_, lean_object* v_cleanupAnnotations_5227_, lean_object* v_whnfType_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5234_; uint8_t v_whnfType_boxed_5235_; lean_object* v_res_5236_; 
v_cleanupAnnotations_boxed_5234_ = lean_unbox(v_cleanupAnnotations_5227_);
v_whnfType_boxed_5235_ = lean_unbox(v_whnfType_5228_);
v_res_5236_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5223_, v_type_5224_, v_maxFVars_x3f_5225_, v_k_5226_, v_cleanupAnnotations_boxed_5234_, v_whnfType_boxed_5235_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
return v_res_5236_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5237_, lean_object* v_as_5238_, size_t v_i_5239_, size_t v_stop_5240_){
_start:
{
uint8_t v___x_5241_; 
v___x_5241_ = lean_usize_dec_eq(v_i_5239_, v_stop_5240_);
if (v___x_5241_ == 0)
{
lean_object* v___x_5242_; uint8_t v___x_5243_; 
v___x_5242_ = lean_array_uget_borrowed(v_as_5238_, v_i_5239_);
v___x_5243_ = lean_expr_eqv(v_a_5237_, v___x_5242_);
if (v___x_5243_ == 0)
{
size_t v___x_5244_; size_t v___x_5245_; 
v___x_5244_ = ((size_t)1ULL);
v___x_5245_ = lean_usize_add(v_i_5239_, v___x_5244_);
v_i_5239_ = v___x_5245_;
goto _start;
}
else
{
return v___x_5243_;
}
}
else
{
uint8_t v___x_5247_; 
v___x_5247_ = 0;
return v___x_5247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5248_, lean_object* v_as_5249_, lean_object* v_i_5250_, lean_object* v_stop_5251_){
_start:
{
size_t v_i_boxed_5252_; size_t v_stop_boxed_5253_; uint8_t v_res_5254_; lean_object* v_r_5255_; 
v_i_boxed_5252_ = lean_unbox_usize(v_i_5250_);
lean_dec(v_i_5250_);
v_stop_boxed_5253_ = lean_unbox_usize(v_stop_5251_);
lean_dec(v_stop_5251_);
v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5248_, v_as_5249_, v_i_boxed_5252_, v_stop_boxed_5253_);
lean_dec_ref(v_as_5249_);
lean_dec_ref(v_a_5248_);
v_r_5255_ = lean_box(v_res_5254_);
return v_r_5255_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; uint8_t v___x_5260_; 
v___x_5258_ = lean_unsigned_to_nat(0u);
v___x_5259_ = lean_array_get_size(v_as_5256_);
v___x_5260_ = lean_nat_dec_lt(v___x_5258_, v___x_5259_);
if (v___x_5260_ == 0)
{
return v___x_5260_;
}
else
{
if (v___x_5260_ == 0)
{
return v___x_5260_;
}
else
{
size_t v___x_5261_; size_t v___x_5262_; uint8_t v___x_5263_; 
v___x_5261_ = ((size_t)0ULL);
v___x_5262_ = lean_usize_of_nat(v___x_5259_);
v___x_5263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5257_, v_as_5256_, v___x_5261_, v___x_5262_);
return v___x_5263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5264_, lean_object* v_a_5265_){
_start:
{
uint8_t v_res_5266_; lean_object* v_r_5267_; 
v_res_5266_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5264_, v_a_5265_);
lean_dec_ref(v_a_5265_);
lean_dec_ref(v_as_5264_);
v_r_5267_ = lean_box(v_res_5266_);
return v_r_5267_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5268_, lean_object* v_e_5269_){
_start:
{
uint8_t v___x_5270_; lean_object* v_d_5272_; lean_object* v_b_5273_; 
v___x_5270_ = l_Lean_Expr_hasFVar(v_e_5269_);
if (v___x_5270_ == 0)
{
lean_dec_ref(v_e_5269_);
return v___x_5270_;
}
else
{
switch(lean_obj_tag(v_e_5269_))
{
case 7:
{
lean_object* v_binderType_5276_; lean_object* v_body_5277_; 
v_binderType_5276_ = lean_ctor_get(v_e_5269_, 1);
lean_inc_ref(v_binderType_5276_);
v_body_5277_ = lean_ctor_get(v_e_5269_, 2);
lean_inc_ref(v_body_5277_);
lean_dec_ref_known(v_e_5269_, 3);
v_d_5272_ = v_binderType_5276_;
v_b_5273_ = v_body_5277_;
goto v___jp_5271_;
}
case 6:
{
lean_object* v_binderType_5278_; lean_object* v_body_5279_; 
v_binderType_5278_ = lean_ctor_get(v_e_5269_, 1);
lean_inc_ref(v_binderType_5278_);
v_body_5279_ = lean_ctor_get(v_e_5269_, 2);
lean_inc_ref(v_body_5279_);
lean_dec_ref_known(v_e_5269_, 3);
v_d_5272_ = v_binderType_5278_;
v_b_5273_ = v_body_5279_;
goto v___jp_5271_;
}
case 10:
{
lean_object* v_expr_5280_; 
v_expr_5280_ = lean_ctor_get(v_e_5269_, 1);
lean_inc_ref(v_expr_5280_);
lean_dec_ref_known(v_e_5269_, 2);
v_e_5269_ = v_expr_5280_;
goto _start;
}
case 8:
{
lean_object* v_type_5282_; lean_object* v_value_5283_; lean_object* v_body_5284_; uint8_t v___x_5285_; 
v_type_5282_ = lean_ctor_get(v_e_5269_, 1);
lean_inc_ref(v_type_5282_);
v_value_5283_ = lean_ctor_get(v_e_5269_, 2);
lean_inc_ref(v_value_5283_);
v_body_5284_ = lean_ctor_get(v_e_5269_, 3);
lean_inc_ref(v_body_5284_);
lean_dec_ref_known(v_e_5269_, 4);
v___x_5285_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5268_, v_type_5282_);
if (v___x_5285_ == 0)
{
uint8_t v___x_5286_; 
v___x_5286_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5268_, v_value_5283_);
if (v___x_5286_ == 0)
{
v_e_5269_ = v_body_5284_;
goto _start;
}
else
{
lean_dec_ref(v_body_5284_);
return v___x_5270_;
}
}
else
{
lean_dec_ref(v_body_5284_);
lean_dec_ref(v_value_5283_);
return v___x_5270_;
}
}
case 5:
{
lean_object* v_fn_5288_; lean_object* v_arg_5289_; uint8_t v___x_5290_; 
v_fn_5288_ = lean_ctor_get(v_e_5269_, 0);
lean_inc_ref(v_fn_5288_);
v_arg_5289_ = lean_ctor_get(v_e_5269_, 1);
lean_inc_ref(v_arg_5289_);
lean_dec_ref_known(v_e_5269_, 2);
v___x_5290_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5268_, v_fn_5288_);
if (v___x_5290_ == 0)
{
v_e_5269_ = v_arg_5289_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5289_);
return v___x_5270_;
}
}
case 11:
{
lean_object* v_struct_5292_; 
v_struct_5292_ = lean_ctor_get(v_e_5269_, 2);
lean_inc_ref(v_struct_5292_);
lean_dec_ref_known(v_e_5269_, 3);
v_e_5269_ = v_struct_5292_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; 
v_fvarId_5294_ = lean_ctor_get(v_e_5269_, 0);
lean_inc(v_fvarId_5294_);
lean_dec_ref_known(v_e_5269_, 1);
v___x_5295_ = l_Lean_Expr_fvar___override(v_fvarId_5294_);
v___x_5296_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5268_, v___x_5295_);
lean_dec_ref(v___x_5295_);
return v___x_5296_;
}
default: 
{
uint8_t v___x_5297_; 
lean_dec_ref(v_e_5269_);
v___x_5297_ = 0;
return v___x_5297_;
}
}
}
v___jp_5271_:
{
uint8_t v___x_5274_; 
v___x_5274_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5268_, v_d_5272_);
if (v___x_5274_ == 0)
{
v_e_5269_ = v_b_5273_;
goto _start;
}
else
{
lean_dec_ref(v_b_5273_);
return v___x_5270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5298_, lean_object* v_e_5299_){
_start:
{
uint8_t v_res_5300_; lean_object* v_r_5301_; 
v_res_5300_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5298_, v_e_5299_);
lean_dec_ref(v_xs_5298_);
v_r_5301_ = lean_box(v_res_5300_);
return v_r_5301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5304_ = l_Lean_stringToMessageData(v___x_5303_);
return v___x_5304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5307_ = l_Lean_stringToMessageData(v___x_5306_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5308_, lean_object* v_type_5309_, lean_object* v_as_5310_, size_t v_sz_5311_, size_t v_i_5312_, lean_object* v_b_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v_a_5320_; uint8_t v___x_5324_; 
v___x_5324_ = lean_usize_dec_lt(v_i_5312_, v_sz_5311_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5325_; 
lean_dec_ref(v_type_5309_);
v___x_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5325_, 0, v_b_5313_);
return v___x_5325_;
}
else
{
lean_object* v___x_5326_; lean_object* v_a_5327_; uint8_t v___x_5328_; 
v___x_5326_ = lean_box(0);
v_a_5327_ = lean_array_uget_borrowed(v_as_5310_, v_i_5312_);
lean_inc(v_a_5327_);
v___x_5328_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5308_, v_a_5327_);
if (v___x_5328_ == 0)
{
v_a_5320_ = v___x_5326_;
goto v___jp_5319_;
}
else
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5327_);
v___x_5330_ = l_Lean_MessageData_ofExpr(v_a_5327_);
v___x_5331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5329_);
lean_ctor_set(v___x_5331_, 1, v___x_5330_);
v___x_5332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5331_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
lean_inc_ref(v_type_5309_);
v___x_5334_ = l_Lean_MessageData_ofExpr(v_type_5309_);
v___x_5335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5335_, 0, v___x_5333_);
lean_ctor_set(v___x_5335_, 1, v___x_5334_);
v___x_5336_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5335_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_dec_ref_known(v___x_5336_, 1);
v_a_5320_ = v___x_5326_;
goto v___jp_5319_;
}
else
{
lean_dec_ref(v_type_5309_);
return v___x_5336_;
}
}
}
v___jp_5319_:
{
size_t v___x_5321_; size_t v___x_5322_; 
v___x_5321_ = ((size_t)1ULL);
v___x_5322_ = lean_usize_add(v_i_5312_, v___x_5321_);
v_i_5312_ = v___x_5322_;
v_b_5313_ = v_a_5320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5337_, lean_object* v_type_5338_, lean_object* v_as_5339_, lean_object* v_sz_5340_, lean_object* v_i_5341_, lean_object* v_b_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
size_t v_sz_boxed_5348_; size_t v_i_boxed_5349_; lean_object* v_res_5350_; 
v_sz_boxed_5348_ = lean_unbox_usize(v_sz_5340_);
lean_dec(v_sz_5340_);
v_i_boxed_5349_ = lean_unbox_usize(v_i_5341_);
lean_dec(v_i_5341_);
v_res_5350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5337_, v_type_5338_, v_as_5339_, v_sz_boxed_5348_, v_i_boxed_5349_, v_b_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec_ref(v_as_5339_);
lean_dec_ref(v_xs_5337_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5351_, size_t v_i_5352_, lean_object* v_bs_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
uint8_t v___x_5359_; 
v___x_5359_ = lean_usize_dec_lt(v_i_5352_, v_sz_5351_);
if (v___x_5359_ == 0)
{
lean_object* v___x_5360_; 
v___x_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5360_, 0, v_bs_5353_);
return v___x_5360_;
}
else
{
lean_object* v_v_5361_; lean_object* v___x_5362_; 
v_v_5361_ = lean_array_uget_borrowed(v_bs_5353_, v_i_5352_);
lean_inc(v___y_5357_);
lean_inc_ref(v___y_5356_);
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5354_);
lean_inc(v_v_5361_);
v___x_5362_ = lean_infer_type(v_v_5361_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v___x_5364_; lean_object* v_bs_x27_5365_; size_t v___x_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_a_5363_);
lean_dec_ref_known(v___x_5362_, 1);
v___x_5364_ = lean_unsigned_to_nat(0u);
v_bs_x27_5365_ = lean_array_uset(v_bs_5353_, v_i_5352_, v___x_5364_);
v___x_5366_ = ((size_t)1ULL);
v___x_5367_ = lean_usize_add(v_i_5352_, v___x_5366_);
v___x_5368_ = lean_array_uset(v_bs_x27_5365_, v_i_5352_, v_a_5363_);
v_i_5352_ = v___x_5367_;
v_bs_5353_ = v___x_5368_;
goto _start;
}
else
{
lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
lean_dec_ref(v_bs_5353_);
v_a_5370_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5362_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5362_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5370_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5378_, lean_object* v_i_5379_, lean_object* v_bs_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
size_t v_sz_boxed_5386_; size_t v_i_boxed_5387_; lean_object* v_res_5388_; 
v_sz_boxed_5386_ = lean_unbox_usize(v_sz_5378_);
lean_dec(v_sz_5378_);
v_i_boxed_5387_ = lean_unbox_usize(v_i_5379_);
lean_dec(v_i_5379_);
v_res_5388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5386_, v_i_boxed_5387_, v_bs_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
return v_res_5388_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5390_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5391_ = l_Lean_stringToMessageData(v___x_5390_);
return v___x_5391_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5393_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5394_ = l_Lean_stringToMessageData(v___x_5393_);
return v___x_5394_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5397_ = l_Lean_stringToMessageData(v___x_5396_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5398_, lean_object* v_n_5399_, lean_object* v_xs_5400_, lean_object* v_x_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
lean_object* v___x_5431_; uint8_t v___x_5432_; 
v___x_5431_ = lean_array_get_size(v_xs_5400_);
v___x_5432_ = lean_nat_dec_eq(v___x_5431_, v_n_5399_);
if (v___x_5432_ == 0)
{
lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_dec_ref(v_xs_5400_);
v___x_5433_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5434_ = l_Lean_MessageData_ofExpr(v_type_5398_);
v___x_5435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = l_Nat_reprFast(v_n_5399_);
v___x_5439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5439_, 0, v___x_5438_);
v___x_5440_ = l_Lean_MessageData_ofFormat(v___x_5439_);
v___x_5441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5437_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5441_);
lean_ctor_set(v___x_5443_, 1, v___x_5442_);
v___x_5444_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5443_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5444_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5445_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
else
{
lean_dec(v_n_5399_);
goto v___jp_5407_;
}
v___jp_5407_:
{
size_t v_sz_5408_; size_t v___x_5409_; lean_object* v___x_5410_; 
v_sz_5408_ = lean_array_size(v_xs_5400_);
v___x_5409_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5400_);
v___x_5410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5408_, v___x_5409_, v_xs_5400_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_object* v_a_5411_; lean_object* v___x_5412_; size_t v_sz_5413_; lean_object* v___x_5414_; 
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
lean_inc(v_a_5411_);
lean_dec_ref_known(v___x_5410_, 1);
v___x_5412_ = lean_box(0);
v_sz_5413_ = lean_array_size(v_a_5411_);
v___x_5414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5400_, v_type_5398_, v_a_5411_, v_sz_5413_, v___x_5409_, v___x_5412_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec_ref(v_xs_5400_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5421_; 
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; 
v_unused_5422_ = lean_ctor_get(v___x_5414_, 0);
lean_dec(v_unused_5422_);
v___x_5416_ = v___x_5414_;
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
else
{
lean_dec(v___x_5414_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5419_; 
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v_a_5411_);
v___x_5419_ = v___x_5416_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5411_);
v___x_5419_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
return v___x_5419_;
}
}
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
lean_dec(v_a_5411_);
v_a_5423_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5414_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5414_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5400_);
lean_dec_ref(v_type_5398_);
return v___x_5410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5453_, lean_object* v_n_5454_, lean_object* v_xs_5455_, lean_object* v_x_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5453_, v_n_5454_, v_xs_5455_, v_x_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec_ref(v_x_5456_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5463_, lean_object* v_type_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v___f_5470_; lean_object* v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; 
lean_inc(v_n_5463_);
lean_inc_ref(v_type_5464_);
v___f_5470_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5470_, 0, v_type_5464_);
lean_closure_set(v___f_5470_, 1, v_n_5463_);
v___x_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5471_, 0, v_n_5463_);
v___x_5472_ = 0;
v___x_5473_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5464_, v___x_5471_, v___f_5470_, v___x_5472_, v___x_5472_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
return v___x_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5474_, lean_object* v_type_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Lean_Meta_arrowDomainsN(v_n_5474_, v_type_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_);
lean_dec(v_a_5479_);
lean_dec_ref(v_a_5478_);
lean_dec(v_a_5477_);
lean_dec_ref(v_a_5476_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5482_, lean_object* v_e_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_){
_start:
{
lean_object* v___x_5489_; 
lean_inc(v_a_5487_);
lean_inc_ref(v_a_5486_);
lean_inc(v_a_5485_);
lean_inc_ref(v_a_5484_);
v___x_5489_ = lean_infer_type(v_e_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; lean_object* v___x_5491_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
lean_inc(v_a_5490_);
lean_dec_ref_known(v___x_5489_, 1);
v___x_5491_ = l_Lean_Meta_arrowDomainsN(v_n_5482_, v_a_5490_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_);
return v___x_5491_;
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec(v_n_5482_);
v_a_5492_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5489_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5489_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5497_; 
if (v_isShared_5495_ == 0)
{
v___x_5497_ = v___x_5494_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_a_5492_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5500_, lean_object* v_e_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_){
_start:
{
lean_object* v_res_5507_; 
v_res_5507_ = l_Lean_Meta_inferArgumentTypesN(v_n_5500_, v_e_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_);
lean_dec(v_a_5505_);
lean_dec_ref(v_a_5504_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
return v_res_5507_;
}
}
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
