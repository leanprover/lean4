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
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_value;
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
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected bound variable "};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_363_ = lean_unsigned_to_nat(99u);
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
v___x_641_ = lean_unsigned_to_nat(39u);
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
lean_object* v___x_1037_; lean_object* v_env_1038_; uint8_t v___y_1040_; uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1037_ = lean_st_ref_get(v___y_1035_);
v_env_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc_ref(v_env_1038_);
lean_dec(v___x_1037_);
v___x_1096_ = l_Lean_Name_isAnonymous(v_declHint_1034_);
v___x_1097_ = lean_bool_not(v___x_1096_);
if (v___x_1097_ == 0)
{
v___y_1040_ = v___x_1097_;
goto v___jp_1039_;
}
else
{
uint8_t v_isExporting_1098_; 
v_isExporting_1098_ = lean_ctor_get_uint8(v_env_1038_, sizeof(void*)*8);
v___y_1040_ = v_isExporting_1098_;
goto v___jp_1039_;
}
v___jp_1039_:
{
if (v___y_1040_ == 0)
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
uint8_t v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = 0;
lean_inc_ref(v_env_1038_);
v___x_1043_ = l_Lean_Environment_setExporting(v_env_1038_, v___x_1042_);
lean_inc(v_declHint_1034_);
lean_inc_ref(v___x_1043_);
v___x_1044_ = l_Lean_Environment_contains(v___x_1043_, v_declHint_1034_, v___y_1040_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_msg_1033_);
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
lean_inc(v_declHint_1034_);
v___x_1050_ = l_Lean_MessageData_ofConstName(v_declHint_1034_, v___x_1042_);
v_c_1051_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1051_, 0, v___x_1049_);
lean_ctor_set(v_c_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1038_, v_declHint_1034_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v_env_1038_);
lean_dec(v_declHint_1034_);
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
lean_ctor_set(v___x_1058_, 0, v_msg_1033_);
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
v___x_1065_ = l_Lean_Environment_header(v_env_1038_);
lean_dec_ref(v_env_1038_);
v___x_1066_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1065_);
v_mod_1067_ = lean_array_get(v___x_1064_, v___x_1066_, v_val_1060_);
lean_dec(v_val_1060_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = l_Lean_isPrivateName(v_declHint_1034_);
lean_dec(v_declHint_1034_);
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
lean_ctor_set(v___x_1078_, 0, v_msg_1033_);
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
lean_ctor_set(v___x_1091_, 0, v_msg_1033_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1099_, lean_object* v_declHint_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1099_, v_declHint_1100_, v___y_1101_);
lean_dec(v___y_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1104_, lean_object* v_declHint_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1121_; 
v___x_1111_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1104_, v_declHint_1105_, v___y_1109_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = l_Lean_unknownIdentifierMessageTag;
v___x_1117_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1117_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1122_, lean_object* v_declHint_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1122_, v_declHint_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1130_, lean_object* v_msg_1131_, lean_object* v_declHint_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v_a_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1131_, v_declHint_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1130_, v_a_1139_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1141_, lean_object* v_msg_1142_, lean_object* v_declHint_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1141_, v_msg_1142_, v_declHint_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_ref_1141_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1156_, lean_object* v_constName_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1163_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1164_ = 0;
lean_inc(v_constName_1157_);
v___x_1165_ = l_Lean_MessageData_ofConstName(v_constName_1157_, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1163_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1156_, v___x_1168_, v_constName_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1170_, lean_object* v_constName_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1170_, v_constName_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_ref_1170_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_ref_1184_; lean_object* v___x_1185_; 
v_ref_1184_ = lean_ctor_get(v___y_1181_, 5);
v___x_1185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1184_, v_constName_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v_env_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = lean_st_ref_get(v___y_1197_);
v_env_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_ref(v_env_1200_);
lean_dec(v___x_1199_);
v___x_1201_ = 0;
lean_inc(v_constName_1193_);
v___x_1202_ = l_Lean_Environment_findConstVal_x3f(v_env_1200_, v_constName_1193_, v___x_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1203_;
}
else
{
lean_object* v_val_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_constName_1193_);
v_val_1204_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1202_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_val_1204_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 0);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_val_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1219_, lean_object* v_us_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___x_1226_; 
lean_inc(v_c_1219_);
v___x_1226_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1219_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_levelParams_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_levelParams_1228_ = lean_ctor_get(v_a_1227_, 1);
v___x_1229_ = l_List_lengthTR___redArg(v_levelParams_1228_);
v___x_1230_ = l_List_lengthTR___redArg(v_us_1220_);
v___x_1231_ = lean_nat_dec_eq(v___x_1229_, v___x_1230_);
lean_dec(v___x_1230_);
lean_dec(v___x_1229_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_a_1227_);
v___x_1232_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1219_, v_us_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; 
lean_dec(v_c_1219_);
v___x_1233_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1227_, v_us_1220_, v_a_1224_);
return v___x_1233_;
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_us_1220_);
lean_dec(v_c_1219_);
v_a_1234_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1226_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1226_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1242_, lean_object* v_us_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1242_, v_us_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1250_, lean_object* v_constName_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1258_, v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1266_, lean_object* v_ref_1267_, lean_object* v_constName_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1267_, v_constName_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1275_, v_ref_1276_, v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v_ref_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v_msg_1286_, lean_object* v_declHint_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1285_, v_msg_1286_, v_declHint_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_ref_1295_, lean_object* v_msg_1296_, lean_object* v_declHint_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1294_, v_ref_1295_, v_msg_1296_, v_declHint_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v_ref_1295_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1304_, v_declHint_1305_, v___y_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1312_, lean_object* v_declHint_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1312_, v_declHint_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1320_, lean_object* v_ref_1321_, lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1321_, v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_ref_1330_, lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1329_, v_ref_1330_, v_msg_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v_ref_1330_);
return v_res_1337_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1344_, lean_object* v_idx_1345_, lean_object* v_e_1346_, lean_object* v_a_1347_, lean_object* v_00_u03b1_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1355_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1356_ = l_Lean_mkProj(v_structName_1344_, v_idx_1345_, v_e_1346_);
v___x_1357_ = l_Lean_indentExpr(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1355_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_indentExpr(v_a_1347_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1362_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1364_, lean_object* v_idx_1365_, lean_object* v_e_1366_, lean_object* v_a_1367_, lean_object* v_00_u03b1_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1364_, v_idx_1365_, v_e_1366_, v_a_1367_, v_00_u03b1_1368_, v_x_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_env_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_st_ref_get(v___y_1380_);
v_env_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_env_1383_);
lean_dec(v___x_1382_);
v___x_1384_ = 0;
lean_inc(v_constName_1376_);
v___x_1385_ = l_Lean_Environment_find_x3f(v_env_1383_, v_constName_1376_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_constName_1376_);
v_val_1387_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 0);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1402_, lean_object* v_structName_1403_, lean_object* v_e_1404_, lean_object* v_idx_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_a_1415_; uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_lt(v_a_1407_, v_upperBound_1402_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_idx_1405_);
lean_dec_ref(v_e_1404_);
lean_dec(v_structName_1403_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_b_1408_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; 
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
v___x_1421_ = lean_whnf(v_b_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
if (lean_obj_tag(v_a_1422_) == 7)
{
lean_object* v_body_1423_; uint8_t v___x_1424_; 
v_body_1423_ = lean_ctor_get(v_a_1422_, 2);
lean_inc_ref(v_body_1423_);
lean_dec_ref_known(v_a_1422_, 3);
v___x_1424_ = l_Lean_Expr_hasLooseBVars(v_body_1423_);
if (v___x_1424_ == 0)
{
v_a_1415_ = v_body_1423_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_inc_ref(v_e_1404_);
lean_inc(v_a_1407_);
lean_inc(v_structName_1403_);
v___x_1425_ = l_Lean_mkProj(v_structName_1403_, v_a_1407_, v_e_1404_);
v___x_1426_ = lean_expr_instantiate1(v_body_1423_, v___x_1425_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v_body_1423_);
v_a_1415_ = v___x_1426_;
goto v___jp_1414_;
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1404_);
lean_inc(v_idx_1405_);
lean_inc(v_structName_1403_);
v___x_1428_ = l_Lean_mkProj(v_structName_1403_, v_idx_1405_, v_e_1404_);
v___x_1429_ = l_Lean_indentExpr(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1427_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_inc_ref(v_a_1406_);
v___x_1433_ = l_Lean_indentExpr(v_a_1406_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1434_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v_a_1415_ = v_a_1422_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_a_1422_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_idx_1405_);
lean_dec_ref(v_e_1404_);
lean_dec(v_structName_1403_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_idx_1405_);
lean_dec_ref(v_e_1404_);
lean_dec(v_structName_1403_);
return v___x_1421_;
}
}
v___jp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_a_1407_, v___x_1416_);
lean_dec(v_a_1407_);
v_a_1407_ = v___x_1417_;
v_b_1408_ = v_a_1415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1444_, lean_object* v_structName_1445_, lean_object* v_e_1446_, lean_object* v_idx_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1444_, v_structName_1445_, v_e_1446_, v_idx_1447_, v_a_1448_, v_a_1449_, v_b_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v_upperBound_1444_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1457_, lean_object* v_structName_1458_, lean_object* v_e_1459_, lean_object* v_idx_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_a_1470_; uint8_t v___x_1474_; 
v___x_1474_ = lean_nat_dec_lt(v_a_1462_, v_upperBound_1457_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_idx_1460_);
lean_dec_ref(v_e_1459_);
lean_dec(v_structName_1458_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_b_1463_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; 
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
v___x_1476_ = lean_whnf(v_b_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
if (lean_obj_tag(v_a_1477_) == 7)
{
lean_object* v_body_1478_; uint8_t v___x_1479_; 
v_body_1478_ = lean_ctor_get(v_a_1477_, 2);
lean_inc_ref(v_body_1478_);
lean_dec_ref_known(v_a_1477_, 3);
v___x_1479_ = l_Lean_Expr_hasLooseBVars(v_body_1478_);
if (v___x_1479_ == 0)
{
v_a_1470_ = v_body_1478_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v_e_1459_);
lean_inc(v_a_1462_);
lean_inc(v_structName_1458_);
v___x_1480_ = l_Lean_mkProj(v_structName_1458_, v_a_1462_, v_e_1459_);
v___x_1481_ = lean_expr_instantiate1(v_body_1478_, v___x_1480_);
lean_dec_ref(v___x_1480_);
lean_dec_ref(v_body_1478_);
v_a_1470_ = v___x_1481_;
goto v___jp_1469_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1459_);
lean_inc(v_idx_1460_);
lean_inc(v_structName_1458_);
v___x_1483_ = l_Lean_mkProj(v_structName_1458_, v_idx_1460_, v_e_1459_);
v___x_1484_ = l_Lean_indentExpr(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1482_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
lean_inc_ref(v_a_1461_);
v___x_1488_ = l_Lean_indentExpr(v_a_1461_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1489_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec_ref_known(v___x_1490_, 1);
v_a_1470_ = v_a_1477_;
goto v___jp_1469_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_a_1477_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_idx_1460_);
lean_dec_ref(v_e_1459_);
lean_dec(v_structName_1458_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
else
{
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_idx_1460_);
lean_dec_ref(v_e_1459_);
lean_dec(v_structName_1458_);
return v___x_1476_;
}
}
v___jp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = lean_nat_add(v_a_1462_, v___x_1471_);
lean_dec(v_a_1462_);
v___x_1473_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1457_, v_structName_1458_, v_e_1459_, v_idx_1460_, v_a_1461_, v___x_1472_, v_a_1470_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1499_, lean_object* v_structName_1500_, lean_object* v_e_1501_, lean_object* v_idx_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1499_, v_structName_1500_, v_e_1501_, v_idx_1502_, v_a_1503_, v_a_1504_, v_b_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v_upperBound_1499_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1512_; lean_object* v_dummy_1513_; 
v___x_1512_ = lean_box(0);
v_dummy_1513_ = l_Lean_Expr_sort___override(v___x_1512_);
return v_dummy_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1514_, lean_object* v_idx_1515_, lean_object* v_e_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
lean_inc_ref(v_e_1516_);
v___x_1522_ = lean_infer_type(v_e_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
v___x_1524_ = lean_whnf(v_a_1523_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_Expr_getAppFn(v_a_1525_);
if (lean_obj_tag(v___x_1526_) == 4)
{
lean_object* v_declName_1527_; lean_object* v_us_1528_; lean_object* v___x_1529_; lean_object* v_env_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_declName_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_declName_1527_);
v_us_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc(v_us_1528_);
lean_dec_ref_known(v___x_1526_, 2);
v___x_1529_ = lean_st_ref_get(v_a_1520_);
v_env_1533_ = lean_ctor_get(v___x_1529_, 0);
lean_inc_ref(v_env_1533_);
lean_dec(v___x_1529_);
v___x_1534_ = 0;
v___x_1535_ = l_Lean_Environment_find_x3f(v_env_1533_, v_declName_1527_, v___x_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_us_1528_);
v___x_1536_ = lean_box(0);
v___x_1537_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1536_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1537_;
}
else
{
lean_object* v_val_1538_; 
v_val_1538_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v___x_1535_, 1);
if (lean_obj_tag(v_val_1538_) == 5)
{
lean_object* v_val_1539_; lean_object* v_ctors_1540_; 
v_val_1539_ = lean_ctor_get(v_val_1538_, 0);
lean_inc_ref(v_val_1539_);
lean_dec_ref_known(v_val_1538_, 1);
v_ctors_1540_ = lean_ctor_get(v_val_1539_, 4);
lean_inc(v_ctors_1540_);
if (lean_obj_tag(v_ctors_1540_) == 1)
{
lean_object* v_tail_1541_; 
v_tail_1541_ = lean_ctor_get(v_ctors_1540_, 1);
if (lean_obj_tag(v_tail_1541_) == 0)
{
lean_object* v_toConstantVal_1542_; lean_object* v_numParams_1543_; lean_object* v_numIndices_1544_; lean_object* v_head_1545_; lean_object* v___x_1546_; 
v_toConstantVal_1542_ = lean_ctor_get(v_val_1539_, 0);
lean_inc_ref(v_toConstantVal_1542_);
v_numParams_1543_ = lean_ctor_get(v_val_1539_, 1);
lean_inc(v_numParams_1543_);
v_numIndices_1544_ = lean_ctor_get(v_val_1539_, 2);
lean_inc(v_numIndices_1544_);
lean_dec_ref(v_val_1539_);
v_head_1545_ = lean_ctor_get(v_ctors_1540_, 0);
lean_inc(v_head_1545_);
lean_dec_ref_known(v_ctors_1540_, 2);
v___x_1546_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1545_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
if (lean_obj_tag(v_a_1547_) == 6)
{
lean_object* v_val_1548_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v_name_1589_; uint8_t v___x_1590_; 
v_val_1548_ = lean_ctor_get(v_a_1547_, 0);
lean_inc_ref(v_val_1548_);
lean_dec_ref_known(v_a_1547_, 1);
v_name_1589_ = lean_ctor_get(v_toConstantVal_1542_, 0);
lean_inc(v_name_1589_);
lean_dec_ref(v_toConstantVal_1542_);
v___x_1590_ = lean_name_eq(v_name_1589_, v_structName_1514_);
lean_dec(v_name_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_val_1548_);
lean_dec(v_numIndices_1544_);
lean_dec(v_numParams_1543_);
lean_dec(v_us_1528_);
v___x_1591_ = lean_box(0);
v___x_1592_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1591_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
v___y_1550_ = v_a_1517_;
v___y_1551_ = v_a_1518_;
v___y_1552_ = v_a_1519_;
v___y_1553_ = v_a_1520_;
goto v___jp_1549_;
}
v___jp_1549_:
{
lean_object* v_dummy_1554_; lean_object* v_nargs_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; uint8_t v___x_1563_; 
v_dummy_1554_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1555_ = l_Lean_Expr_getAppNumArgs(v_a_1525_);
lean_inc(v_nargs_1555_);
v___x_1556_ = lean_mk_array(v_nargs_1555_, v_dummy_1554_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_sub(v_nargs_1555_, v___x_1557_);
lean_dec(v_nargs_1555_);
lean_inc(v_a_1525_);
v___x_1559_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1525_, v___x_1556_, v___x_1558_);
v___x_1560_ = lean_nat_add(v_numParams_1543_, v_numIndices_1544_);
lean_dec(v_numIndices_1544_);
v___x_1561_ = lean_array_get_size(v___x_1559_);
v___x_1562_ = lean_nat_dec_eq(v___x_1560_, v___x_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_bool_not(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v_toConstantVal_1564_; lean_object* v_name_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_toConstantVal_1564_ = lean_ctor_get(v_val_1548_, 0);
lean_inc_ref(v_toConstantVal_1564_);
lean_dec_ref(v_val_1548_);
v_name_1565_ = lean_ctor_get(v_toConstantVal_1564_, 0);
lean_inc(v_name_1565_);
lean_dec_ref(v_toConstantVal_1564_);
v___x_1566_ = l_Lean_mkConst(v_name_1565_, v_us_1528_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = l_Array_toSubarray___redArg(v___x_1559_, v___x_1567_, v_numParams_1543_);
v___x_1569_ = l_Subarray_copy___redArg(v___x_1568_);
v___x_1570_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1566_, v___x_1569_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec_ref(v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
lean_inc(v_a_1525_);
lean_inc_ref(v_e_1516_);
lean_inc(v_structName_1514_);
lean_inc(v_idx_1515_);
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1515_, v_structName_1514_, v_e_1516_, v_idx_1515_, v_a_1525_, v___x_1567_, v_a_1571_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
v___x_1574_ = lean_whnf(v_a_1573_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
if (lean_obj_tag(v_a_1575_) == 7)
{
lean_object* v_binderType_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
v_binderType_1579_ = lean_ctor_get(v_a_1575_, 1);
lean_inc_ref(v_binderType_1579_);
lean_dec_ref_known(v_a_1575_, 3);
v___x_1580_ = lean_expr_consume_type_annotations(v_binderType_1579_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1580_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_del_object(v___x_1577_);
lean_dec(v_a_1575_);
v___x_1584_ = lean_box(0);
v___x_1585_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1584_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1585_;
}
}
}
else
{
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
return v___x_1574_;
}
}
else
{
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
return v___x_1572_;
}
}
else
{
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
return v___x_1570_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v___x_1559_);
lean_dec_ref(v_val_1548_);
lean_dec(v_numParams_1543_);
lean_dec(v_us_1528_);
v___x_1587_ = lean_box(0);
v___x_1588_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1587_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1588_;
}
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v_a_1547_);
lean_dec(v_numIndices_1544_);
lean_dec(v_numParams_1543_);
lean_dec_ref(v_toConstantVal_1542_);
lean_dec(v_us_1528_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1601_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1602_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_numIndices_1544_);
lean_dec(v_numParams_1543_);
lean_dec_ref(v_toConstantVal_1542_);
lean_dec(v_us_1528_);
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
v_a_1603_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1546_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1546_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1540_, 2);
lean_dec_ref(v_val_1539_);
lean_dec(v_us_1528_);
goto v___jp_1530_;
}
}
else
{
lean_dec(v_ctors_1540_);
lean_dec_ref(v_val_1539_);
lean_dec(v_us_1528_);
goto v___jp_1530_;
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec(v_val_1538_);
lean_dec(v_us_1528_);
v___x_1611_ = lean_box(0);
v___x_1612_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1611_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1612_;
}
}
v___jp_1530_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1531_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1532_;
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v___x_1526_);
v___x_1613_ = lean_box(0);
v___x_1614_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1514_, v_idx_1515_, v_e_1516_, v_a_1525_, lean_box(0), v___x_1613_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1614_;
}
}
else
{
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
return v___x_1524_;
}
}
else
{
lean_dec_ref(v_e_1516_);
lean_dec(v_idx_1515_);
lean_dec(v_structName_1514_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1615_, lean_object* v_idx_1616_, lean_object* v_e_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1615_, v_idx_1616_, v_e_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1624_, lean_object* v_structName_1625_, lean_object* v_e_1626_, lean_object* v_idx_1627_, lean_object* v_a_1628_, lean_object* v_inst_1629_, lean_object* v_R_1630_, lean_object* v_a_1631_, lean_object* v_b_1632_, lean_object* v_c_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1624_, v_structName_1625_, v_e_1626_, v_idx_1627_, v_a_1628_, v_a_1631_, v_b_1632_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1640_, lean_object* v_structName_1641_, lean_object* v_e_1642_, lean_object* v_idx_1643_, lean_object* v_a_1644_, lean_object* v_inst_1645_, lean_object* v_R_1646_, lean_object* v_a_1647_, lean_object* v_b_1648_, lean_object* v_c_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1640_, v_structName_1641_, v_e_1642_, v_idx_1643_, v_a_1644_, v_inst_1645_, v_R_1646_, v_a_1647_, v_b_1648_, v_c_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_upperBound_1640_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1656_, lean_object* v_structName_1657_, lean_object* v_e_1658_, lean_object* v_idx_1659_, lean_object* v_a_1660_, lean_object* v_inst_1661_, lean_object* v_R_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_c_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1656_, v_structName_1657_, v_e_1658_, v_idx_1659_, v_a_1660_, v_a_1663_, v_b_1664_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1672_, lean_object* v_structName_1673_, lean_object* v_e_1674_, lean_object* v_idx_1675_, lean_object* v_a_1676_, lean_object* v_inst_1677_, lean_object* v_R_1678_, lean_object* v_a_1679_, lean_object* v_b_1680_, lean_object* v_c_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1672_, v_structName_1673_, v_e_1674_, v_idx_1675_, v_a_1676_, v_inst_1677_, v_R_1678_, v_a_1679_, v_b_1680_, v_c_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v_upperBound_1672_);
return v_res_1687_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1698_ = l_Lean_indentExpr(v_type_1691_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1699_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1708_, lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_type_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1716_, v_type_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v_ks_1728_; lean_object* v_vs_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1753_; 
v_ks_1728_ = lean_ctor_get(v_x_1724_, 0);
v_vs_1729_ = lean_ctor_get(v_x_1724_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1724_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1731_ = v_x_1724_;
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_vs_1729_);
lean_inc(v_ks_1728_);
lean_dec(v_x_1724_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v_ks_1728_);
v___x_1734_ = lean_nat_dec_lt(v_x_1725_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec(v_x_1725_);
v___x_1735_ = lean_array_push(v_ks_1728_, v_x_1726_);
v___x_1736_ = lean_array_push(v_vs_1729_, v_x_1727_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1736_);
lean_ctor_set(v___x_1731_, 0, v___x_1735_);
v___x_1738_ = v___x_1731_;
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
else
{
lean_object* v_k_x27_1740_; uint8_t v___x_1741_; 
v_k_x27_1740_ = lean_array_fget_borrowed(v_ks_1728_, v_x_1725_);
v___x_1741_ = l_Lean_instBEqMVarId_beq(v_x_1726_, v_k_x27_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1743_; 
if (v_isShared_1732_ == 0)
{
v___x_1743_ = v___x_1731_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_ks_1728_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_vs_1729_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v_x_1725_, v___x_1744_);
lean_dec(v_x_1725_);
v_x_1724_ = v___x_1743_;
v_x_1725_ = v___x_1745_;
goto _start;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1748_ = lean_array_fset(v_ks_1728_, v_x_1725_, v_x_1726_);
v___x_1749_ = lean_array_fset(v_vs_1729_, v_x_1725_, v_x_1727_);
lean_dec(v_x_1725_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1749_);
lean_ctor_set(v___x_1731_, 0, v___x_1748_);
v___x_1751_ = v___x_1731_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1754_, lean_object* v_k_1755_, lean_object* v_v_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1754_, v___x_1757_, v_k_1755_, v_v_1756_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1760_, size_t v_x_1761_, size_t v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
if (lean_obj_tag(v_x_1760_) == 0)
{
lean_object* v_es_1765_; size_t v___x_1766_; size_t v___x_1767_; lean_object* v_j_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_es_1765_ = lean_ctor_get(v_x_1760_, 0);
v___x_1766_ = ((size_t)31ULL);
v___x_1767_ = lean_usize_land(v_x_1761_, v___x_1766_);
v_j_1768_ = lean_usize_to_nat(v___x_1767_);
v___x_1769_ = lean_array_get_size(v_es_1765_);
v___x_1770_ = lean_nat_dec_lt(v_j_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec(v_j_1768_);
lean_dec(v_x_1764_);
lean_dec(v_x_1763_);
return v_x_1760_;
}
else
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1809_; 
lean_inc_ref(v_es_1765_);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_x_1760_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_x_1760_, 0);
lean_dec(v_unused_1810_);
v___x_1772_ = v_x_1760_;
v_isShared_1773_ = v_isSharedCheck_1809_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v_x_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1809_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_v_1774_; lean_object* v___x_1775_; lean_object* v_xs_x27_1776_; lean_object* v___y_1778_; 
v_v_1774_ = lean_array_fget(v_es_1765_, v_j_1768_);
v___x_1775_ = lean_box(0);
v_xs_x27_1776_ = lean_array_fset(v_es_1765_, v_j_1768_, v___x_1775_);
switch(lean_obj_tag(v_v_1774_))
{
case 0:
{
lean_object* v_key_1783_; lean_object* v_val_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1794_; 
v_key_1783_ = lean_ctor_get(v_v_1774_, 0);
v_val_1784_ = lean_ctor_get(v_v_1774_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_v_1774_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1786_ = v_v_1774_;
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_val_1784_);
lean_inc(v_key_1783_);
lean_dec(v_v_1774_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
uint8_t v___x_1788_; 
v___x_1788_ = l_Lean_instBEqMVarId_beq(v_x_1763_, v_key_1783_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_del_object(v___x_1786_);
v___x_1789_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1783_, v_val_1784_, v_x_1763_, v_x_1764_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___y_1778_ = v___x_1790_;
goto v___jp_1777_;
}
else
{
lean_object* v___x_1792_; 
lean_dec(v_val_1784_);
lean_dec(v_key_1783_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v_x_1764_);
lean_ctor_set(v___x_1786_, 0, v_x_1763_);
v___x_1792_ = v___x_1786_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_x_1763_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_x_1764_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1778_ = v___x_1792_;
goto v___jp_1777_;
}
}
}
}
case 1:
{
lean_object* v_node_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1807_; 
v_node_1795_ = lean_ctor_get(v_v_1774_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_v_1774_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1797_ = v_v_1774_;
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_node_1795_);
lean_dec(v_v_1774_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
size_t v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1799_ = ((size_t)5ULL);
v___x_1800_ = lean_usize_shift_right(v_x_1761_, v___x_1799_);
v___x_1801_ = ((size_t)1ULL);
v___x_1802_ = lean_usize_add(v_x_1762_, v___x_1801_);
v___x_1803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1795_, v___x_1800_, v___x_1802_, v_x_1763_, v_x_1764_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1803_);
v___x_1805_ = v___x_1797_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
v___y_1778_ = v___x_1805_;
goto v___jp_1777_;
}
}
}
default: 
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_x_1763_);
lean_ctor_set(v___x_1808_, 1, v_x_1764_);
v___y_1778_ = v___x_1808_;
goto v___jp_1777_;
}
}
v___jp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_array_fset(v_xs_x27_1776_, v_j_1768_, v___y_1778_);
lean_dec(v_j_1768_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1779_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
else
{
lean_object* v_ks_1811_; lean_object* v_vs_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1832_; 
v_ks_1811_ = lean_ctor_get(v_x_1760_, 0);
v_vs_1812_ = lean_ctor_get(v_x_1760_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_x_1760_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1814_ = v_x_1760_;
v_isShared_1815_ = v_isSharedCheck_1832_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_vs_1812_);
lean_inc(v_ks_1811_);
lean_dec(v_x_1760_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1832_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_ks_1811_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_vs_1812_);
v___x_1817_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v_newNode_1818_; uint8_t v___y_1820_; size_t v___x_1826_; uint8_t v___x_1827_; 
v_newNode_1818_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1817_, v_x_1763_, v_x_1764_);
v___x_1826_ = ((size_t)7ULL);
v___x_1827_ = lean_usize_dec_le(v___x_1826_, v_x_1762_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1828_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1818_);
v___x_1829_ = lean_unsigned_to_nat(4u);
v___x_1830_ = lean_nat_dec_lt(v___x_1828_, v___x_1829_);
lean_dec(v___x_1828_);
v___y_1820_ = v___x_1830_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v___x_1827_;
goto v___jp_1819_;
}
v___jp_1819_:
{
if (v___y_1820_ == 0)
{
lean_object* v_ks_1821_; lean_object* v_vs_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_ks_1821_ = lean_ctor_get(v_newNode_1818_, 0);
lean_inc_ref(v_ks_1821_);
v_vs_1822_ = lean_ctor_get(v_newNode_1818_, 1);
lean_inc_ref(v_vs_1822_);
lean_dec_ref(v_newNode_1818_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1762_, v_ks_1821_, v_vs_1822_, v___x_1823_, v___x_1824_);
lean_dec_ref(v_vs_1822_);
lean_dec_ref(v_ks_1821_);
return v___x_1825_;
}
else
{
return v_newNode_1818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1833_, lean_object* v_keys_1834_, lean_object* v_vals_1835_, lean_object* v_i_1836_, lean_object* v_entries_1837_){
_start:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_keys_1834_);
v___x_1839_ = lean_nat_dec_lt(v_i_1836_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec(v_i_1836_);
return v_entries_1837_;
}
else
{
lean_object* v_k_1840_; lean_object* v_v_1841_; uint64_t v___x_1842_; size_t v_h_1843_; size_t v___x_1844_; lean_object* v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; size_t v_h_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_k_1840_ = lean_array_fget_borrowed(v_keys_1834_, v_i_1836_);
v_v_1841_ = lean_array_fget_borrowed(v_vals_1835_, v_i_1836_);
v___x_1842_ = l_Lean_instHashableMVarId_hash(v_k_1840_);
v_h_1843_ = lean_uint64_to_usize(v___x_1842_);
v___x_1844_ = ((size_t)5ULL);
v___x_1845_ = lean_unsigned_to_nat(1u);
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_sub(v_depth_1833_, v___x_1846_);
v___x_1848_ = lean_usize_mul(v___x_1844_, v___x_1847_);
v_h_1849_ = lean_usize_shift_right(v_h_1843_, v___x_1848_);
v___x_1850_ = lean_nat_add(v_i_1836_, v___x_1845_);
lean_dec(v_i_1836_);
lean_inc(v_v_1841_);
lean_inc(v_k_1840_);
v___x_1851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1837_, v_h_1849_, v_depth_1833_, v_k_1840_, v_v_1841_);
v_i_1836_ = v___x_1850_;
v_entries_1837_ = v___x_1851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1853_, lean_object* v_keys_1854_, lean_object* v_vals_1855_, lean_object* v_i_1856_, lean_object* v_entries_1857_){
_start:
{
size_t v_depth_boxed_1858_; lean_object* v_res_1859_; 
v_depth_boxed_1858_ = lean_unbox_usize(v_depth_1853_);
lean_dec(v_depth_1853_);
v_res_1859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1858_, v_keys_1854_, v_vals_1855_, v_i_1856_, v_entries_1857_);
lean_dec_ref(v_vals_1855_);
lean_dec_ref(v_keys_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
size_t v_x_1230__boxed_1865_; size_t v_x_1231__boxed_1866_; lean_object* v_res_1867_; 
v_x_1230__boxed_1865_ = lean_unbox_usize(v_x_1861_);
lean_dec(v_x_1861_);
v_x_1231__boxed_1866_ = lean_unbox_usize(v_x_1862_);
lean_dec(v_x_1862_);
v_res_1867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1860_, v_x_1230__boxed_1865_, v_x_1231__boxed_1866_, v_x_1863_, v_x_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
uint64_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = l_Lean_instHashableMVarId_hash(v_x_1869_);
v___x_1872_ = lean_uint64_to_usize(v___x_1871_);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1868_, v___x_1872_, v___x_1873_, v_x_1869_, v_x_1870_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1875_, lean_object* v_val_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v_mctx_1880_; lean_object* v_cache_1881_; lean_object* v_zetaDeltaFVarIds_1882_; lean_object* v_postponed_1883_; lean_object* v_diag_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1912_; 
v___x_1879_ = lean_st_ref_take(v___y_1877_);
v_mctx_1880_ = lean_ctor_get(v___x_1879_, 0);
v_cache_1881_ = lean_ctor_get(v___x_1879_, 1);
v_zetaDeltaFVarIds_1882_ = lean_ctor_get(v___x_1879_, 2);
v_postponed_1883_ = lean_ctor_get(v___x_1879_, 3);
v_diag_1884_ = lean_ctor_get(v___x_1879_, 4);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1886_ = v___x_1879_;
v_isShared_1887_ = v_isSharedCheck_1912_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_diag_1884_);
lean_inc(v_postponed_1883_);
lean_inc(v_zetaDeltaFVarIds_1882_);
lean_inc(v_cache_1881_);
lean_inc(v_mctx_1880_);
lean_dec(v___x_1879_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1912_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_depth_1888_; lean_object* v_levelAssignDepth_1889_; lean_object* v_lmvarCounter_1890_; lean_object* v_mvarCounter_1891_; lean_object* v_lDecls_1892_; lean_object* v_decls_1893_; lean_object* v_userNames_1894_; lean_object* v_lAssignment_1895_; lean_object* v_eAssignment_1896_; lean_object* v_dAssignment_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1911_; 
v_depth_1888_ = lean_ctor_get(v_mctx_1880_, 0);
v_levelAssignDepth_1889_ = lean_ctor_get(v_mctx_1880_, 1);
v_lmvarCounter_1890_ = lean_ctor_get(v_mctx_1880_, 2);
v_mvarCounter_1891_ = lean_ctor_get(v_mctx_1880_, 3);
v_lDecls_1892_ = lean_ctor_get(v_mctx_1880_, 4);
v_decls_1893_ = lean_ctor_get(v_mctx_1880_, 5);
v_userNames_1894_ = lean_ctor_get(v_mctx_1880_, 6);
v_lAssignment_1895_ = lean_ctor_get(v_mctx_1880_, 7);
v_eAssignment_1896_ = lean_ctor_get(v_mctx_1880_, 8);
v_dAssignment_1897_ = lean_ctor_get(v_mctx_1880_, 9);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_mctx_1880_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1899_ = v_mctx_1880_;
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_dAssignment_1897_);
lean_inc(v_eAssignment_1896_);
lean_inc(v_lAssignment_1895_);
lean_inc(v_userNames_1894_);
lean_inc(v_decls_1893_);
lean_inc(v_lDecls_1892_);
lean_inc(v_mvarCounter_1891_);
lean_inc(v_lmvarCounter_1890_);
lean_inc(v_levelAssignDepth_1889_);
lean_inc(v_depth_1888_);
lean_dec(v_mctx_1880_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1896_, v_mvarId_1875_, v_val_1876_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 8, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_depth_1888_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_levelAssignDepth_1889_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_lmvarCounter_1890_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_mvarCounter_1891_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_lDecls_1892_);
lean_ctor_set(v_reuseFailAlloc_1910_, 5, v_decls_1893_);
lean_ctor_set(v_reuseFailAlloc_1910_, 6, v_userNames_1894_);
lean_ctor_set(v_reuseFailAlloc_1910_, 7, v_lAssignment_1895_);
lean_ctor_set(v_reuseFailAlloc_1910_, 8, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 9, v_dAssignment_1897_);
v___x_1903_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1903_);
v___x_1905_ = v___x_1886_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_cache_1881_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_zetaDeltaFVarIds_1882_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_postponed_1883_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v_diag_1884_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_st_ref_set(v___y_1877_, v___x_1905_);
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1913_, lean_object* v_val_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1913_, v_val_1914_, v___y_1915_);
lean_dec(v___y_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1924_; 
lean_inc(v_a_1922_);
lean_inc_ref(v_a_1921_);
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc_ref(v_type_1918_);
v___x_1924_ = lean_infer_type(v_type_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l_Lean_Meta_whnfD(v_a_1925_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1961_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1961_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1961_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
switch(lean_obj_tag(v_a_1927_))
{
case 3:
{
lean_object* v_u_1931_; lean_object* v___x_1933_; 
lean_dec_ref(v_type_1918_);
v_u_1931_ = lean_ctor_get(v_a_1927_, 0);
lean_inc(v_u_1931_);
lean_dec_ref_known(v_a_1927_, 1);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v_u_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_u_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
case 2:
{
lean_object* v_mvarId_1935_; lean_object* v___x_1936_; 
lean_del_object(v___x_1929_);
v_mvarId_1935_ = lean_ctor_get(v_a_1927_, 0);
lean_inc_n(v_mvarId_1935_, 2);
lean_dec_ref_known(v_a_1927_, 1);
v___x_1936_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1935_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; uint8_t v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v_type_1918_);
v___x_1939_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_n(v_a_1940_, 2);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = l_Lean_mkSort(v_a_1940_);
v___x_1942_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1935_, v___x_1941_, v_a_1920_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_1950_);
v___x_1944_ = v___x_1942_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_dec(v___x_1942_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_a_1940_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1940_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_dec(v_mvarId_1935_);
return v___x_1939_;
}
}
else
{
lean_object* v___x_1951_; 
lean_dec(v_mvarId_1935_);
v___x_1951_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
return v___x_1951_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_mvarId_1935_);
lean_dec_ref(v_type_1918_);
v_a_1952_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1936_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1936_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
default: 
{
lean_object* v___x_1960_; 
lean_del_object(v___x_1929_);
lean_dec(v_a_1927_);
v___x_1960_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_type_1918_);
v_a_1962_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1926_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1926_);
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
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_type_1918_);
v_a_1970_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1924_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1924_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_getLevel(v_type_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1985_, lean_object* v_val_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1985_, v_val_1986_, v___y_1988_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1993_, lean_object* v_val_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1993_, v_val_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2002_, v_x_2003_, v_x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2006_, lean_object* v_x_2007_, size_t v_x_2008_, size_t v_x_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2007_, v_x_2008_, v_x_2009_, v_x_2010_, v_x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
size_t v_x_1583__boxed_2019_; size_t v_x_1584__boxed_2020_; lean_object* v_res_2021_; 
v_x_1583__boxed_2019_ = lean_unbox_usize(v_x_2015_);
lean_dec(v_x_2015_);
v_x_1584__boxed_2020_ = lean_unbox_usize(v_x_2016_);
lean_dec(v_x_2016_);
v_res_2021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2013_, v_x_2014_, v_x_1583__boxed_2019_, v_x_1584__boxed_2020_, v_x_2017_, v_x_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2022_, lean_object* v_n_2023_, lean_object* v_k_2024_, lean_object* v_v_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2023_, v_k_2024_, v_v_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2027_, size_t v_depth_2028_, lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_heq_2031_, lean_object* v_i_2032_, lean_object* v_entries_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2028_, v_keys_2029_, v_vals_2030_, v_i_2032_, v_entries_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2035_, lean_object* v_depth_2036_, lean_object* v_keys_2037_, lean_object* v_vals_2038_, lean_object* v_heq_2039_, lean_object* v_i_2040_, lean_object* v_entries_2041_){
_start:
{
size_t v_depth_boxed_2042_; lean_object* v_res_2043_; 
v_depth_boxed_2042_ = lean_unbox_usize(v_depth_2036_);
lean_dec(v_depth_2036_);
v_res_2043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2035_, v_depth_boxed_2042_, v_keys_2037_, v_vals_2038_, v_heq_2039_, v_i_2040_, v_entries_2041_);
lean_dec_ref(v_vals_2038_);
lean_dec_ref(v_keys_2037_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2045_, v_x_2046_, v_x_2047_, v_x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2050_, lean_object* v_b_2051_, lean_object* v_c_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
v___x_2058_ = lean_apply_7(v_k_2050_, v_b_2051_, v_c_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, lean_box(0));
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2059_, lean_object* v_b_2060_, lean_object* v_c_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2059_, v_b_2060_, v_c_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2068_, lean_object* v_k_2069_, uint8_t v_cleanupAnnotations_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___f_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2076_, 0, v_k_2069_);
v___x_2077_ = 0;
v___x_2078_ = lean_box(0);
v___x_2079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2077_, v___x_2078_, v_type_2068_, v___f_2076_, v_cleanupAnnotations_2070_, v___x_2077_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
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
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2079_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2079_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2096_, lean_object* v_k_2097_, lean_object* v_cleanupAnnotations_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2104_; lean_object* v_res_2105_; 
v_cleanupAnnotations_boxed_2104_ = lean_unbox(v_cleanupAnnotations_2098_);
v_res_2105_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2096_, v_k_2097_, v_cleanupAnnotations_boxed_2104_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2106_, lean_object* v_type_2107_, lean_object* v_k_2108_, uint8_t v_cleanupAnnotations_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2107_, v_k_2108_, v_cleanupAnnotations_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_type_2117_, lean_object* v_k_2118_, lean_object* v_cleanupAnnotations_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2125_; lean_object* v_res_2126_; 
v_cleanupAnnotations_boxed_2125_ = lean_unbox(v_cleanupAnnotations_2119_);
v_res_2126_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2116_, v_type_2117_, v_k_2118_, v_cleanupAnnotations_boxed_2125_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2127_, size_t v_i_2128_, size_t v_stop_2129_, lean_object* v_b_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_usize_dec_eq(v_i_2128_, v_stop_2129_);
if (v___x_2136_ == 0)
{
size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_sub(v_i_2128_, v___x_2137_);
v___x_2139_ = lean_array_uget_borrowed(v_as_2127_, v___x_2138_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___y_2132_);
lean_inc_ref(v___y_2131_);
lean_inc(v___x_2139_);
v___x_2140_ = lean_infer_type(v___x_2139_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l_Lean_Meta_getLevel(v_a_2141_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_mkLevelIMax_x27(v_a_2143_, v_b_2130_);
v_i_2128_ = v___x_2138_;
v_b_2130_ = v___x_2144_;
goto _start;
}
else
{
lean_dec(v_b_2130_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2146_; 
v_a_2146_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2142_, 1);
v_i_2128_ = v___x_2138_;
v_b_2130_ = v_a_2146_;
goto _start;
}
else
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_b_2130_);
v_a_2148_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2140_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2140_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_b_2130_);
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2157_, lean_object* v_i_2158_, lean_object* v_stop_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
size_t v_i_boxed_2166_; size_t v_stop_boxed_2167_; lean_object* v_res_2168_; 
v_i_boxed_2166_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_stop_boxed_2167_ = lean_unbox_usize(v_stop_2159_);
lean_dec(v_stop_2159_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2157_, v_i_boxed_2166_, v_stop_boxed_2167_, v_b_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_as_2157_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2169_, lean_object* v_e_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___y_2177_; lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Meta_getLevel(v_e_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
v___x_2198_ = lean_array_get_size(v_xs_2169_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_lt(v___x_2199_, v___x_2198_);
if (v___x_2200_ == 0)
{
lean_dec(v_a_2197_);
v___y_2177_ = v___x_2196_;
goto v___jp_2176_;
}
else
{
size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
lean_dec_ref_known(v___x_2196_, 1);
v___x_2201_ = lean_usize_of_nat(v___x_2198_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2169_, v___x_2201_, v___x_2202_, v_a_2197_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
v___y_2177_ = v___x_2203_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2196_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2196_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
v___jp_2176_:
{
if (lean_obj_tag(v___y_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2187_; 
v_a_2178_ = lean_ctor_get(v___y_2177_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___y_2177_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2180_ = v___y_2177_;
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___y_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = l_Lean_Level_normalize(v_a_2178_);
lean_dec(v_a_2178_);
v___x_2183_ = l_Lean_mkSort(v___x_2182_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2183_);
v___x_2185_ = v___x_2180_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___y_2177_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___y_2177_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___y_2177_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___y_2177_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2212_, lean_object* v_e_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2212_, v_e_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_xs_2212_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___f_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; 
v___f_2227_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2228_ = 0;
v___x_2229_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2221_, v___f_2227_, v___x_2228_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2237_, lean_object* v_k_2238_, uint8_t v_cleanupAnnotations_2239_, uint8_t v_preserveNondepLet_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___f_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___f_2246_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2246_, 0, v_k_2238_);
v___x_2247_ = 1;
v___x_2248_ = 0;
v___x_2249_ = lean_box(0);
v___x_2250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2237_, v___x_2247_, v___x_2247_, v_preserveNondepLet_2240_, v___x_2248_, v___x_2249_, v___f_2246_, v_cleanupAnnotations_2239_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
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
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2250_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2250_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2267_, lean_object* v_k_2268_, lean_object* v_cleanupAnnotations_2269_, lean_object* v_preserveNondepLet_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2276_; uint8_t v_preserveNondepLet_boxed_2277_; lean_object* v_res_2278_; 
v_cleanupAnnotations_boxed_2276_ = lean_unbox(v_cleanupAnnotations_2269_);
v_preserveNondepLet_boxed_2277_ = lean_unbox(v_preserveNondepLet_2270_);
v_res_2278_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2267_, v_k_2268_, v_cleanupAnnotations_boxed_2276_, v_preserveNondepLet_boxed_2277_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2279_, lean_object* v_e_2280_, lean_object* v_k_2281_, uint8_t v_cleanupAnnotations_2282_, uint8_t v_preserveNondepLet_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2280_, v_k_2281_, v_cleanupAnnotations_2282_, v_preserveNondepLet_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_e_2291_, lean_object* v_k_2292_, lean_object* v_cleanupAnnotations_2293_, lean_object* v_preserveNondepLet_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2300_; uint8_t v_preserveNondepLet_boxed_2301_; lean_object* v_res_2302_; 
v_cleanupAnnotations_boxed_2300_ = lean_unbox(v_cleanupAnnotations_2293_);
v_preserveNondepLet_boxed_2301_ = lean_unbox(v_preserveNondepLet_2294_);
v_res_2302_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2290_, v_e_2291_, v_k_2292_, v_cleanupAnnotations_boxed_2300_, v_preserveNondepLet_boxed_2301_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2303_, lean_object* v_e_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
lean_inc(v___y_2306_);
lean_inc_ref(v___y_2305_);
v___x_2310_ = lean_infer_type(v_e_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; uint8_t v___x_2312_; uint8_t v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = 0;
v___x_2313_ = 1;
v___x_2314_ = 1;
v___x_2315_ = l_Lean_Meta_mkForallFVars(v_xs_2303_, v_a_2311_, v___x_2312_, v___x_2313_, v___x_2312_, v___x_2314_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2315_;
}
else
{
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2316_, lean_object* v_e_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2316_, v_e_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_xs_2316_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___f_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v___f_2331_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2332_ = 0;
v___x_2333_ = 1;
v___x_2334_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2325_, v___f_2331_, v___x_2332_, v___x_2333_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2354_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2355_ = l_Lean_MessageData_ofName(v_mvarId_2348_);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2358_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2367_, lean_object* v_mvarId_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_mvarId_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2375_, v_mvarId_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v_mctx_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_st_ref_get(v_a_2385_);
v_mctx_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_ref(v_mctx_2390_);
lean_dec(v___x_2389_);
v___x_2391_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2390_, v_mvarId_2383_);
lean_dec_ref(v_mctx_2390_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2392_;
}
else
{
lean_object* v_val_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_mvarId_2383_);
v_val_2393_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_val_2393_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_type_2397_; lean_object* v___x_2399_; 
v_type_2397_ = lean_ctor_get(v_val_2393_, 2);
lean_inc_ref(v_type_2397_);
lean_dec(v_val_2393_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set_tag(v___x_2395_, 0);
lean_ctor_set(v___x_2395_, 0, v_type_2397_);
v___x_2399_ = v___x_2395_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_type_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_lctx_2414_; lean_object* v___x_2415_; 
v_lctx_2414_ = lean_ctor_get(v_a_2410_, 2);
lean_inc(v_fvarId_2409_);
lean_inc_ref(v_lctx_2414_);
v___x_2415_ = lean_local_ctx_find(v_lctx_2414_, v_fvarId_2409_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2409_, v_a_2411_, v_a_2412_);
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_fvarId_2409_);
v_val_2417_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_val_2417_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = l_Lean_LocalDecl_type(v_val_2417_);
lean_dec(v_val_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set_tag(v___x_2419_, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec_ref(v_a_2427_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2432_, v_a_2433_, v_a_2435_, v_a_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2(void){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_instMonadEIO(lean_box(0));
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2);
v___x_2450_ = l_StateRefT_x27_instMonad___redArg(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2453_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___f_2455_; 
v___x_2454_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2455_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2455_, 0, v___x_2454_);
return v___f_2455_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___f_2457_; 
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2457_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2457_, 0, v___x_2456_);
return v___f_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___f_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; 
v___f_2458_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___f_2459_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___f_2459_);
lean_ctor_set(v___x_2460_, 1, v___f_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___f_2462_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2462_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2462_, 0, v___x_2461_);
return v___f_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___f_2464_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2464_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
return v___f_2464_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12(void){
_start:
{
lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; 
v___f_2465_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11);
v___f_2466_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___f_2466_);
lean_ctor_set(v___x_2467_, 1, v___f_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2468_, lean_object* v_inferType_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v___y_2476_; uint8_t v___y_2519_; uint8_t v_cacheInferType_2625_; uint8_t v___x_2626_; 
v_cacheInferType_2625_ = lean_ctor_get_uint8(v_a_2470_, sizeof(void*)*7 + 3);
v___x_2626_ = lean_bool_not(v_cacheInferType_2625_);
if (v___x_2626_ == 0)
{
uint8_t v___x_2627_; 
v___x_2627_ = l_Lean_Expr_hasMVar(v_e_2468_);
v___y_2519_ = v___x_2627_;
goto v___jp_2518_;
}
else
{
v___y_2519_ = v___x_2626_;
goto v___jp_2518_;
}
v___jp_2475_:
{
lean_object* v___x_2477_; 
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
v___x_2477_ = lean_apply_5(v_inferType_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, lean_box(0));
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; uint8_t v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
v___x_2479_ = l_Lean_Expr_hasMVar(v_a_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2516_; 
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2477_, 0);
lean_dec(v_unused_2517_);
v___x_2481_ = v___x_2477_;
v_isShared_2482_ = v_isSharedCheck_2516_;
goto v_resetjp_2480_;
}
else
{
lean_dec(v___x_2477_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2516_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v_cache_2484_; lean_object* v_mctx_2485_; lean_object* v_zetaDeltaFVarIds_2486_; lean_object* v_postponed_2487_; lean_object* v_diag_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2515_; 
v___x_2483_ = lean_st_ref_take(v_a_2471_);
v_cache_2484_ = lean_ctor_get(v___x_2483_, 1);
v_mctx_2485_ = lean_ctor_get(v___x_2483_, 0);
v_zetaDeltaFVarIds_2486_ = lean_ctor_get(v___x_2483_, 2);
v_postponed_2487_ = lean_ctor_get(v___x_2483_, 3);
v_diag_2488_ = lean_ctor_get(v___x_2483_, 4);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2490_ = v___x_2483_;
v_isShared_2491_ = v_isSharedCheck_2515_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_diag_2488_);
lean_inc(v_postponed_2487_);
lean_inc(v_zetaDeltaFVarIds_2486_);
lean_inc(v_cache_2484_);
lean_inc(v_mctx_2485_);
lean_dec(v___x_2483_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2515_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_inferType_2492_; lean_object* v_funInfo_2493_; lean_object* v_synthInstance_2494_; lean_object* v_whnf_2495_; lean_object* v_defEqTrans_2496_; lean_object* v_defEqPerm_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2514_; 
v_inferType_2492_ = lean_ctor_get(v_cache_2484_, 0);
v_funInfo_2493_ = lean_ctor_get(v_cache_2484_, 1);
v_synthInstance_2494_ = lean_ctor_get(v_cache_2484_, 2);
v_whnf_2495_ = lean_ctor_get(v_cache_2484_, 3);
v_defEqTrans_2496_ = lean_ctor_get(v_cache_2484_, 4);
v_defEqPerm_2497_ = lean_ctor_get(v_cache_2484_, 5);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_cache_2484_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2499_ = v_cache_2484_;
v_isShared_2500_ = v_isSharedCheck_2514_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_defEqPerm_2497_);
lean_inc(v_defEqTrans_2496_);
lean_inc(v_whnf_2495_);
lean_inc(v_synthInstance_2494_);
lean_inc(v_funInfo_2493_);
lean_inc(v_inferType_2492_);
lean_dec(v_cache_2484_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2514_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___f_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___f_2501_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0));
v___x_2502_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1));
lean_inc(v_a_2478_);
v___x_2503_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2501_, v___x_2502_, v_inferType_2492_, v___y_2476_, v_a_2478_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2503_);
v___x_2505_ = v___x_2499_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_funInfo_2493_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_synthInstance_2494_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_whnf_2495_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_defEqTrans_2496_);
lean_ctor_set(v_reuseFailAlloc_2513_, 5, v_defEqPerm_2497_);
v___x_2505_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 1, v___x_2505_);
v___x_2507_ = v___x_2490_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_mctx_2485_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_zetaDeltaFVarIds_2486_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_postponed_2487_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_diag_2488_);
v___x_2507_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_st_ref_set(v_a_2471_, v___x_2507_);
if (v_isShared_2482_ == 0)
{
v___x_2510_ = v___x_2481_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2478_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2478_);
lean_dec_ref(v___y_2476_);
return v___x_2477_;
}
}
else
{
lean_dec_ref(v___y_2476_);
return v___x_2477_;
}
}
v___jp_2518_:
{
if (v___y_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2468_, v_a_2470_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2579_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2579_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2579_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v_cache_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2574_; 
v___x_2525_ = lean_st_ref_get(v_a_2471_);
v_cache_2526_ = lean_ctor_get(v___x_2525_, 1);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; lean_object* v_unused_2576_; lean_object* v_unused_2577_; lean_object* v_unused_2578_; 
v_unused_2575_ = lean_ctor_get(v___x_2525_, 4);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v___x_2525_, 3);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v___x_2525_, 2);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v___x_2525_, 0);
lean_dec(v_unused_2578_);
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2574_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_cache_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2574_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_inferType_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_inferType_2530_ = lean_ctor_get(v_cache_2526_, 0);
lean_inc_ref(v_inferType_2530_);
lean_dec_ref(v_cache_2526_);
v___f_2531_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0));
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1));
lean_inc(v_a_2521_);
v___x_2533_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2531_, v___x_2532_, v_inferType_2530_, v_a_2521_);
lean_dec_ref(v_inferType_2530_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; lean_object* v_toApplicative_2535_; lean_object* v_toFunctor_2536_; lean_object* v_toSeq_2537_; lean_object* v_toSeqLeft_2538_; lean_object* v_toSeqRight_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2549_; 
lean_del_object(v___x_2523_);
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3);
v_toApplicative_2535_ = lean_ctor_get(v___x_2534_, 0);
v_toFunctor_2536_ = lean_ctor_get(v_toApplicative_2535_, 0);
v_toSeq_2537_ = lean_ctor_get(v_toApplicative_2535_, 2);
v_toSeqLeft_2538_ = lean_ctor_get(v_toApplicative_2535_, 3);
v_toSeqRight_2539_ = lean_ctor_get(v_toApplicative_2535_, 4);
v___f_2540_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4));
v___f_2541_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5));
lean_inc_ref_n(v_toFunctor_2536_, 2);
v___f_2542_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2542_, 0, v_toFunctor_2536_);
v___f_2543_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2543_, 0, v_toFunctor_2536_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___f_2542_);
lean_ctor_set(v___x_2544_, 1, v___f_2543_);
lean_inc(v_toSeqRight_2539_);
v___f_2545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2545_, 0, v_toSeqRight_2539_);
lean_inc(v_toSeqLeft_2538_);
v___f_2546_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2546_, 0, v_toSeqLeft_2538_);
lean_inc(v_toSeq_2537_);
v___f_2547_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2547_, 0, v_toSeq_2537_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v___f_2545_);
lean_ctor_set(v___x_2528_, 3, v___f_2546_);
lean_ctor_set(v___x_2528_, 2, v___f_2547_);
lean_ctor_set(v___x_2528_, 1, v___f_2540_);
lean_ctor_set(v___x_2528_, 0, v___x_2544_);
v___x_2549_ = v___x_2528_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v___f_2540_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v___f_2547_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v___f_2546_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v___f_2545_);
v___x_2549_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v_cancelTk_x3f_2551_; 
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___f_2541_);
v_cancelTk_x3f_2551_ = lean_ctor_get(v_a_2472_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2551_) == 1)
{
lean_object* v_val_2552_; uint8_t v___x_2553_; 
v_val_2552_ = lean_ctor_get(v_cancelTk_x3f_2551_, 0);
v___x_2553_ = l_IO_CancelToken_isSet(v_val_2552_);
if (v___x_2553_ == 0)
{
lean_dec_ref_known(v___x_2550_, 2);
v___y_2476_ = v_a_2521_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2110__overap_2559_; lean_object* v___x_2560_; 
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12);
v___x_2555_ = l_Lean_Core_instMonadRefCoreM;
v___x_2556_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2557_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2556_, v___x_2550_);
v___x_2558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2554_);
lean_ctor_set(v___x_2558_, 1, v___x_2555_);
lean_ctor_set(v___x_2558_, 2, v___x_2557_);
v___x_2110__overap_2559_ = l_Lean_throwInterruptException___redArg(v___x_2558_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2560_ = lean_apply_3(v___x_2110__overap_2559_, v_a_2472_, v_a_2473_, lean_box(0));
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_dec_ref_known(v___x_2560_, 1);
v___y_2476_ = v_a_2521_;
goto v___jp_2475_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2521_);
lean_dec_ref(v_inferType_2469_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2550_, 2);
v___y_2476_ = v_a_2521_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_val_2570_; lean_object* v___x_2572_; 
lean_del_object(v___x_2528_);
lean_dec(v_a_2521_);
lean_dec_ref(v_inferType_2469_);
v_val_2570_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_val_2570_);
lean_dec_ref_known(v___x_2533_, 1);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v_val_2570_);
v___x_2572_ = v___x_2523_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_val_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v_inferType_2469_);
v_a_2580_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2520_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2520_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v___x_2588_; lean_object* v_toApplicative_2589_; lean_object* v_toFunctor_2590_; lean_object* v_toSeq_2591_; lean_object* v_toSeqLeft_2592_; lean_object* v_toSeqRight_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_cancelTk_x3f_2604_; 
lean_dec_ref(v_e_2468_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3);
v_toApplicative_2589_ = lean_ctor_get(v___x_2588_, 0);
v_toFunctor_2590_ = lean_ctor_get(v_toApplicative_2589_, 0);
v_toSeq_2591_ = lean_ctor_get(v_toApplicative_2589_, 2);
v_toSeqLeft_2592_ = lean_ctor_get(v_toApplicative_2589_, 3);
v_toSeqRight_2593_ = lean_ctor_get(v_toApplicative_2589_, 4);
v___f_2594_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4));
v___f_2595_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5));
lean_inc_ref_n(v_toFunctor_2590_, 2);
v___f_2596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2596_, 0, v_toFunctor_2590_);
v___f_2597_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2597_, 0, v_toFunctor_2590_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___f_2596_);
lean_ctor_set(v___x_2598_, 1, v___f_2597_);
lean_inc(v_toSeqRight_2593_);
v___f_2599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2599_, 0, v_toSeqRight_2593_);
lean_inc(v_toSeqLeft_2592_);
v___f_2600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2600_, 0, v_toSeqLeft_2592_);
lean_inc(v_toSeq_2591_);
v___f_2601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2601_, 0, v_toSeq_2591_);
v___x_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2598_);
lean_ctor_set(v___x_2602_, 1, v___f_2594_);
lean_ctor_set(v___x_2602_, 2, v___f_2601_);
lean_ctor_set(v___x_2602_, 3, v___f_2600_);
lean_ctor_set(v___x_2602_, 4, v___f_2599_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___f_2595_);
v_cancelTk_x3f_2604_ = lean_ctor_get(v_a_2472_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2604_) == 1)
{
lean_object* v_val_2605_; uint8_t v___x_2606_; 
v_val_2605_ = lean_ctor_get(v_cancelTk_x3f_2604_, 0);
v___x_2606_ = l_IO_CancelToken_isSet(v_val_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_dec_ref_known(v___x_2603_, 2);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
v___x_2607_ = lean_apply_5(v_inferType_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, lean_box(0));
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2159__overap_2613_; lean_object* v___x_2614_; 
v___x_2608_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12);
v___x_2609_ = l_Lean_Core_instMonadRefCoreM;
v___x_2610_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2611_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2610_, v___x_2603_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2608_);
lean_ctor_set(v___x_2612_, 1, v___x_2609_);
lean_ctor_set(v___x_2612_, 2, v___x_2611_);
v___x_2159__overap_2613_ = l_Lean_throwInterruptException___redArg(v___x_2612_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2614_ = lean_apply_3(v___x_2159__overap_2613_, v_a_2472_, v_a_2473_, lean_box(0));
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2615_; 
lean_dec_ref_known(v___x_2614_, 1);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
v___x_2615_ = lean_apply_5(v_inferType_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, lean_box(0));
return v___x_2615_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_inferType_2469_);
v_a_2616_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2614_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2603_, 2);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
v___x_2624_ = lean_apply_5(v_inferType_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, lean_box(0));
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2628_, lean_object* v_inferType_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2628_, v_inferType_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___y_2643_; uint8_t v___y_2644_; uint8_t v___y_2645_; uint8_t v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; uint8_t v___y_2682_; lean_object* v___x_2740_; uint8_t v_transparency_2741_; uint8_t v___x_2742_; uint8_t v___x_2743_; 
v___x_2740_ = l_Lean_Meta_Context_config(v_a_2637_);
v_transparency_2741_ = lean_ctor_get_uint8(v___x_2740_, 9);
lean_dec_ref(v___x_2740_);
v___x_2742_ = 1;
v___x_2743_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
v___y_2682_ = v_transparency_2741_;
goto v___jp_2681_;
}
else
{
v___y_2682_ = v___x_2742_;
goto v___jp_2681_;
}
v___jp_2642_:
{
lean_object* v___x_2654_; uint8_t v_foApprox_2655_; uint8_t v_ctxApprox_2656_; uint8_t v_quasiPatternApprox_2657_; uint8_t v_constApprox_2658_; uint8_t v_isDefEqStuckEx_2659_; uint8_t v_unificationHints_2660_; uint8_t v_proofIrrelevance_2661_; uint8_t v_assignSyntheticOpaque_2662_; uint8_t v_offsetCnstrs_2663_; uint8_t v_transparency_2664_; uint8_t v_univApprox_2665_; uint8_t v_zetaUnused_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2680_; 
v___x_2654_ = l_Lean_Meta_Context_config(v___y_2643_);
lean_dec_ref(v___y_2643_);
v_foApprox_2655_ = lean_ctor_get_uint8(v___x_2654_, 0);
v_ctxApprox_2656_ = lean_ctor_get_uint8(v___x_2654_, 1);
v_quasiPatternApprox_2657_ = lean_ctor_get_uint8(v___x_2654_, 2);
v_constApprox_2658_ = lean_ctor_get_uint8(v___x_2654_, 3);
v_isDefEqStuckEx_2659_ = lean_ctor_get_uint8(v___x_2654_, 4);
v_unificationHints_2660_ = lean_ctor_get_uint8(v___x_2654_, 5);
v_proofIrrelevance_2661_ = lean_ctor_get_uint8(v___x_2654_, 6);
v_assignSyntheticOpaque_2662_ = lean_ctor_get_uint8(v___x_2654_, 7);
v_offsetCnstrs_2663_ = lean_ctor_get_uint8(v___x_2654_, 8);
v_transparency_2664_ = lean_ctor_get_uint8(v___x_2654_, 9);
v_univApprox_2665_ = lean_ctor_get_uint8(v___x_2654_, 11);
v_zetaUnused_2666_ = lean_ctor_get_uint8(v___x_2654_, 17);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2668_ = v___x_2654_;
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2654_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___x_2670_; uint8_t v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2674_; 
v___x_2670_ = 1;
v___x_2671_ = 0;
v___x_2672_ = 2;
if (v_isShared_2669_ == 0)
{
v___x_2674_ = v___x_2668_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 0, v_foApprox_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 1, v_ctxApprox_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 2, v_quasiPatternApprox_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 3, v_constApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 4, v_isDefEqStuckEx_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 5, v_unificationHints_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 6, v_proofIrrelevance_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 7, v_assignSyntheticOpaque_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 8, v_offsetCnstrs_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 9, v_transparency_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 11, v_univApprox_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 17, v_zetaUnused_2666_);
v___x_2674_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
uint64_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_ctor_set_uint8(v___x_2674_, 10, v___x_2671_);
lean_ctor_set_uint8(v___x_2674_, 12, v___x_2670_);
lean_ctor_set_uint8(v___x_2674_, 13, v___x_2670_);
lean_ctor_set_uint8(v___x_2674_, 14, v___x_2672_);
lean_ctor_set_uint8(v___x_2674_, 15, v___x_2670_);
lean_ctor_set_uint8(v___x_2674_, 16, v___x_2670_);
lean_ctor_set_uint8(v___x_2674_, 18, v___x_2670_);
v___x_2675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2674_);
v___x_2676_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set_uint64(v___x_2676_, sizeof(void*)*1, v___x_2675_);
lean_inc(v___y_2651_);
lean_inc(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2652_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2653_);
v___x_2677_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___y_2653_);
lean_ctor_set(v___x_2677_, 2, v___y_2649_);
lean_ctor_set(v___x_2677_, 3, v___y_2652_);
lean_ctor_set(v___x_2677_, 4, v___y_2647_);
lean_ctor_set(v___x_2677_, 5, v___y_2648_);
lean_ctor_set(v___x_2677_, 6, v___y_2651_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7, v___y_2646_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 1, v___y_2645_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 2, v___y_2644_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*7 + 3, v___y_2650_);
lean_inc(v_a_2640_);
lean_inc_ref(v_a_2639_);
lean_inc(v_a_2638_);
v___x_2678_ = lean_apply_5(v_x_2636_, v___x_2677_, v_a_2638_, v_a_2639_, v_a_2640_, lean_box(0));
return v___x_2678_;
}
}
}
v___jp_2681_:
{
lean_object* v___x_2683_; uint8_t v_foApprox_2684_; uint8_t v_ctxApprox_2685_; uint8_t v_quasiPatternApprox_2686_; uint8_t v_constApprox_2687_; uint8_t v_isDefEqStuckEx_2688_; uint8_t v_unificationHints_2689_; uint8_t v_proofIrrelevance_2690_; uint8_t v_assignSyntheticOpaque_2691_; uint8_t v_offsetCnstrs_2692_; uint8_t v_etaStruct_2693_; uint8_t v_univApprox_2694_; uint8_t v_iota_2695_; uint8_t v_beta_2696_; uint8_t v_proj_2697_; uint8_t v_zeta_2698_; uint8_t v_zetaDelta_2699_; uint8_t v_zetaUnused_2700_; uint8_t v_zetaHave_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2739_; 
v___x_2683_ = l_Lean_Meta_Context_config(v_a_2637_);
v_foApprox_2684_ = lean_ctor_get_uint8(v___x_2683_, 0);
v_ctxApprox_2685_ = lean_ctor_get_uint8(v___x_2683_, 1);
v_quasiPatternApprox_2686_ = lean_ctor_get_uint8(v___x_2683_, 2);
v_constApprox_2687_ = lean_ctor_get_uint8(v___x_2683_, 3);
v_isDefEqStuckEx_2688_ = lean_ctor_get_uint8(v___x_2683_, 4);
v_unificationHints_2689_ = lean_ctor_get_uint8(v___x_2683_, 5);
v_proofIrrelevance_2690_ = lean_ctor_get_uint8(v___x_2683_, 6);
v_assignSyntheticOpaque_2691_ = lean_ctor_get_uint8(v___x_2683_, 7);
v_offsetCnstrs_2692_ = lean_ctor_get_uint8(v___x_2683_, 8);
v_etaStruct_2693_ = lean_ctor_get_uint8(v___x_2683_, 10);
v_univApprox_2694_ = lean_ctor_get_uint8(v___x_2683_, 11);
v_iota_2695_ = lean_ctor_get_uint8(v___x_2683_, 12);
v_beta_2696_ = lean_ctor_get_uint8(v___x_2683_, 13);
v_proj_2697_ = lean_ctor_get_uint8(v___x_2683_, 14);
v_zeta_2698_ = lean_ctor_get_uint8(v___x_2683_, 15);
v_zetaDelta_2699_ = lean_ctor_get_uint8(v___x_2683_, 16);
v_zetaUnused_2700_ = lean_ctor_get_uint8(v___x_2683_, 17);
v_zetaHave_2701_ = lean_ctor_get_uint8(v___x_2683_, 18);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2703_ = v___x_2683_;
v_isShared_2704_ = v_isSharedCheck_2739_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v___x_2683_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2739_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
uint8_t v_trackZetaDelta_2705_; lean_object* v_zetaDeltaSet_2706_; lean_object* v_lctx_2707_; lean_object* v_localInstances_2708_; lean_object* v_defEqCtx_x3f_2709_; lean_object* v_synthPendingDepth_2710_; lean_object* v_canUnfold_x3f_2711_; uint8_t v_univApprox_2712_; uint8_t v_inTypeClassResolution_2713_; uint8_t v_cacheInferType_2714_; lean_object* v_config_2716_; 
v_trackZetaDelta_2705_ = lean_ctor_get_uint8(v_a_2637_, sizeof(void*)*7);
v_zetaDeltaSet_2706_ = lean_ctor_get(v_a_2637_, 1);
v_lctx_2707_ = lean_ctor_get(v_a_2637_, 2);
v_localInstances_2708_ = lean_ctor_get(v_a_2637_, 3);
v_defEqCtx_x3f_2709_ = lean_ctor_get(v_a_2637_, 4);
v_synthPendingDepth_2710_ = lean_ctor_get(v_a_2637_, 5);
v_canUnfold_x3f_2711_ = lean_ctor_get(v_a_2637_, 6);
v_univApprox_2712_ = lean_ctor_get_uint8(v_a_2637_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2713_ = lean_ctor_get_uint8(v_a_2637_, sizeof(void*)*7 + 2);
v_cacheInferType_2714_ = lean_ctor_get_uint8(v_a_2637_, sizeof(void*)*7 + 3);
if (v_isShared_2704_ == 0)
{
v_config_2716_ = v___x_2703_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 0, v_foApprox_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 1, v_ctxApprox_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 2, v_quasiPatternApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 3, v_constApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 4, v_isDefEqStuckEx_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 5, v_unificationHints_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 6, v_proofIrrelevance_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 7, v_assignSyntheticOpaque_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 8, v_offsetCnstrs_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 10, v_etaStruct_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 11, v_univApprox_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 12, v_iota_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 13, v_beta_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 14, v_proj_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 15, v_zeta_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 16, v_zetaDelta_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 17, v_zetaUnused_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, 18, v_zetaHave_2701_);
v_config_2716_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
uint64_t v___x_2717_; uint64_t v___x_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; uint64_t v_key_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v_beta_2726_; 
lean_ctor_set_uint8(v_config_2716_, 9, v___y_2682_);
v___x_2717_ = l_Lean_Meta_Context_configKey(v_a_2637_);
v___x_2718_ = 3ULL;
v___x_2719_ = lean_uint64_shift_right(v___x_2717_, v___x_2718_);
v___x_2720_ = lean_uint64_shift_left(v___x_2719_, v___x_2718_);
v___x_2721_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2682_);
v_key_2722_ = lean_uint64_lor(v___x_2720_, v___x_2721_);
v___x_2723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2723_, 0, v_config_2716_);
lean_ctor_set_uint64(v___x_2723_, sizeof(void*)*1, v_key_2722_);
lean_inc(v_canUnfold_x3f_2711_);
lean_inc(v_synthPendingDepth_2710_);
lean_inc(v_defEqCtx_x3f_2709_);
lean_inc_ref(v_localInstances_2708_);
lean_inc_ref(v_lctx_2707_);
lean_inc(v_zetaDeltaSet_2706_);
v___x_2724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v_zetaDeltaSet_2706_);
lean_ctor_set(v___x_2724_, 2, v_lctx_2707_);
lean_ctor_set(v___x_2724_, 3, v_localInstances_2708_);
lean_ctor_set(v___x_2724_, 4, v_defEqCtx_x3f_2709_);
lean_ctor_set(v___x_2724_, 5, v_synthPendingDepth_2710_);
lean_ctor_set(v___x_2724_, 6, v_canUnfold_x3f_2711_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7, v_trackZetaDelta_2705_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 1, v_univApprox_2712_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2713_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 3, v_cacheInferType_2714_);
v___x_2725_ = l_Lean_Meta_Context_config(v___x_2724_);
v_beta_2726_ = lean_ctor_get_uint8(v___x_2725_, 13);
if (v_beta_2726_ == 0)
{
lean_dec_ref(v___x_2725_);
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v_iota_2727_; 
v_iota_2727_ = lean_ctor_get_uint8(v___x_2725_, 12);
if (v_iota_2727_ == 0)
{
lean_dec_ref(v___x_2725_);
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v_zeta_2728_; 
v_zeta_2728_ = lean_ctor_get_uint8(v___x_2725_, 15);
if (v_zeta_2728_ == 0)
{
lean_dec_ref(v___x_2725_);
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v_zetaHave_2729_; 
v_zetaHave_2729_ = lean_ctor_get_uint8(v___x_2725_, 18);
if (v_zetaHave_2729_ == 0)
{
lean_dec_ref(v___x_2725_);
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v_zetaDelta_2730_; 
v_zetaDelta_2730_ = lean_ctor_get_uint8(v___x_2725_, 16);
if (v_zetaDelta_2730_ == 0)
{
lean_dec_ref(v___x_2725_);
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v_etaStruct_2731_; uint8_t v_proj_2732_; uint8_t v___x_2733_; uint8_t v___x_2734_; 
v_etaStruct_2731_ = lean_ctor_get_uint8(v___x_2725_, 10);
v_proj_2732_ = lean_ctor_get_uint8(v___x_2725_, 14);
lean_dec_ref(v___x_2725_);
v___x_2733_ = 2;
v___x_2734_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
uint8_t v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = 0;
v___x_2736_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2731_, v___x_2735_);
if (v___x_2736_ == 0)
{
v___y_2643_ = v___x_2724_;
v___y_2644_ = v_inTypeClassResolution_2713_;
v___y_2645_ = v_univApprox_2712_;
v___y_2646_ = v_trackZetaDelta_2705_;
v___y_2647_ = v_defEqCtx_x3f_2709_;
v___y_2648_ = v_synthPendingDepth_2710_;
v___y_2649_ = v_lctx_2707_;
v___y_2650_ = v_cacheInferType_2714_;
v___y_2651_ = v_canUnfold_x3f_2711_;
v___y_2652_ = v_localInstances_2708_;
v___y_2653_ = v_zetaDeltaSet_2706_;
goto v___jp_2642_;
}
else
{
lean_object* v___x_2737_; 
lean_inc(v_a_2640_);
lean_inc_ref(v_a_2639_);
lean_inc(v_a_2638_);
v___x_2737_ = lean_apply_5(v_x_2636_, v___x_2724_, v_a_2638_, v_a_2639_, v_a_2640_, lean_box(0));
return v___x_2737_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2751_, lean_object* v_x_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___y_2759_; uint8_t v___y_2760_; uint8_t v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; uint8_t v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; uint8_t v___y_2798_; lean_object* v___x_2856_; uint8_t v_transparency_2857_; uint8_t v___x_2858_; uint8_t v___x_2859_; 
v___x_2856_ = l_Lean_Meta_Context_config(v_a_2753_);
v_transparency_2857_ = lean_ctor_get_uint8(v___x_2856_, 9);
lean_dec_ref(v___x_2856_);
v___x_2858_ = 1;
v___x_2859_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
v___y_2798_ = v_transparency_2857_;
goto v___jp_2797_;
}
else
{
v___y_2798_ = v___x_2858_;
goto v___jp_2797_;
}
v___jp_2758_:
{
lean_object* v___x_2770_; uint8_t v_foApprox_2771_; uint8_t v_ctxApprox_2772_; uint8_t v_quasiPatternApprox_2773_; uint8_t v_constApprox_2774_; uint8_t v_isDefEqStuckEx_2775_; uint8_t v_unificationHints_2776_; uint8_t v_proofIrrelevance_2777_; uint8_t v_assignSyntheticOpaque_2778_; uint8_t v_offsetCnstrs_2779_; uint8_t v_transparency_2780_; uint8_t v_univApprox_2781_; uint8_t v_zetaUnused_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2796_; 
v___x_2770_ = l_Lean_Meta_Context_config(v___y_2759_);
lean_dec_ref(v___y_2759_);
v_foApprox_2771_ = lean_ctor_get_uint8(v___x_2770_, 0);
v_ctxApprox_2772_ = lean_ctor_get_uint8(v___x_2770_, 1);
v_quasiPatternApprox_2773_ = lean_ctor_get_uint8(v___x_2770_, 2);
v_constApprox_2774_ = lean_ctor_get_uint8(v___x_2770_, 3);
v_isDefEqStuckEx_2775_ = lean_ctor_get_uint8(v___x_2770_, 4);
v_unificationHints_2776_ = lean_ctor_get_uint8(v___x_2770_, 5);
v_proofIrrelevance_2777_ = lean_ctor_get_uint8(v___x_2770_, 6);
v_assignSyntheticOpaque_2778_ = lean_ctor_get_uint8(v___x_2770_, 7);
v_offsetCnstrs_2779_ = lean_ctor_get_uint8(v___x_2770_, 8);
v_transparency_2780_ = lean_ctor_get_uint8(v___x_2770_, 9);
v_univApprox_2781_ = lean_ctor_get_uint8(v___x_2770_, 11);
v_zetaUnused_2782_ = lean_ctor_get_uint8(v___x_2770_, 17);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2784_ = v___x_2770_;
v_isShared_2785_ = v_isSharedCheck_2796_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v___x_2770_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2796_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
uint8_t v___x_2786_; uint8_t v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2790_; 
v___x_2786_ = 1;
v___x_2787_ = 0;
v___x_2788_ = 2;
if (v_isShared_2785_ == 0)
{
v___x_2790_ = v___x_2784_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 0, v_foApprox_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 1, v_ctxApprox_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 2, v_quasiPatternApprox_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 3, v_constApprox_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 4, v_isDefEqStuckEx_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 5, v_unificationHints_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 6, v_proofIrrelevance_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 7, v_assignSyntheticOpaque_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 8, v_offsetCnstrs_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 9, v_transparency_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 11, v_univApprox_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2795_, 17, v_zetaUnused_2782_);
v___x_2790_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
uint64_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_ctor_set_uint8(v___x_2790_, 10, v___x_2787_);
lean_ctor_set_uint8(v___x_2790_, 12, v___x_2786_);
lean_ctor_set_uint8(v___x_2790_, 13, v___x_2786_);
lean_ctor_set_uint8(v___x_2790_, 14, v___x_2788_);
lean_ctor_set_uint8(v___x_2790_, 15, v___x_2786_);
lean_ctor_set_uint8(v___x_2790_, 16, v___x_2786_);
lean_ctor_set_uint8(v___x_2790_, 18, v___x_2786_);
v___x_2791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2790_);
v___x_2792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set_uint64(v___x_2792_, sizeof(void*)*1, v___x_2791_);
lean_inc(v___y_2767_);
lean_inc(v___y_2764_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2768_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2769_);
v___x_2793_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___y_2769_);
lean_ctor_set(v___x_2793_, 2, v___y_2765_);
lean_ctor_set(v___x_2793_, 3, v___y_2768_);
lean_ctor_set(v___x_2793_, 4, v___y_2763_);
lean_ctor_set(v___x_2793_, 5, v___y_2764_);
lean_ctor_set(v___x_2793_, 6, v___y_2767_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*7, v___y_2762_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*7 + 1, v___y_2761_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*7 + 2, v___y_2760_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*7 + 3, v___y_2766_);
lean_inc(v_a_2756_);
lean_inc_ref(v_a_2755_);
lean_inc(v_a_2754_);
v___x_2794_ = lean_apply_5(v_x_2752_, v___x_2793_, v_a_2754_, v_a_2755_, v_a_2756_, lean_box(0));
return v___x_2794_;
}
}
}
v___jp_2797_:
{
lean_object* v___x_2799_; uint8_t v_foApprox_2800_; uint8_t v_ctxApprox_2801_; uint8_t v_quasiPatternApprox_2802_; uint8_t v_constApprox_2803_; uint8_t v_isDefEqStuckEx_2804_; uint8_t v_unificationHints_2805_; uint8_t v_proofIrrelevance_2806_; uint8_t v_assignSyntheticOpaque_2807_; uint8_t v_offsetCnstrs_2808_; uint8_t v_etaStruct_2809_; uint8_t v_univApprox_2810_; uint8_t v_iota_2811_; uint8_t v_beta_2812_; uint8_t v_proj_2813_; uint8_t v_zeta_2814_; uint8_t v_zetaDelta_2815_; uint8_t v_zetaUnused_2816_; uint8_t v_zetaHave_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2855_; 
v___x_2799_ = l_Lean_Meta_Context_config(v_a_2753_);
v_foApprox_2800_ = lean_ctor_get_uint8(v___x_2799_, 0);
v_ctxApprox_2801_ = lean_ctor_get_uint8(v___x_2799_, 1);
v_quasiPatternApprox_2802_ = lean_ctor_get_uint8(v___x_2799_, 2);
v_constApprox_2803_ = lean_ctor_get_uint8(v___x_2799_, 3);
v_isDefEqStuckEx_2804_ = lean_ctor_get_uint8(v___x_2799_, 4);
v_unificationHints_2805_ = lean_ctor_get_uint8(v___x_2799_, 5);
v_proofIrrelevance_2806_ = lean_ctor_get_uint8(v___x_2799_, 6);
v_assignSyntheticOpaque_2807_ = lean_ctor_get_uint8(v___x_2799_, 7);
v_offsetCnstrs_2808_ = lean_ctor_get_uint8(v___x_2799_, 8);
v_etaStruct_2809_ = lean_ctor_get_uint8(v___x_2799_, 10);
v_univApprox_2810_ = lean_ctor_get_uint8(v___x_2799_, 11);
v_iota_2811_ = lean_ctor_get_uint8(v___x_2799_, 12);
v_beta_2812_ = lean_ctor_get_uint8(v___x_2799_, 13);
v_proj_2813_ = lean_ctor_get_uint8(v___x_2799_, 14);
v_zeta_2814_ = lean_ctor_get_uint8(v___x_2799_, 15);
v_zetaDelta_2815_ = lean_ctor_get_uint8(v___x_2799_, 16);
v_zetaUnused_2816_ = lean_ctor_get_uint8(v___x_2799_, 17);
v_zetaHave_2817_ = lean_ctor_get_uint8(v___x_2799_, 18);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2819_ = v___x_2799_;
v_isShared_2820_ = v_isSharedCheck_2855_;
goto v_resetjp_2818_;
}
else
{
lean_dec(v___x_2799_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2855_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
uint8_t v_trackZetaDelta_2821_; lean_object* v_zetaDeltaSet_2822_; lean_object* v_lctx_2823_; lean_object* v_localInstances_2824_; lean_object* v_defEqCtx_x3f_2825_; lean_object* v_synthPendingDepth_2826_; lean_object* v_canUnfold_x3f_2827_; uint8_t v_univApprox_2828_; uint8_t v_inTypeClassResolution_2829_; uint8_t v_cacheInferType_2830_; lean_object* v_config_2832_; 
v_trackZetaDelta_2821_ = lean_ctor_get_uint8(v_a_2753_, sizeof(void*)*7);
v_zetaDeltaSet_2822_ = lean_ctor_get(v_a_2753_, 1);
v_lctx_2823_ = lean_ctor_get(v_a_2753_, 2);
v_localInstances_2824_ = lean_ctor_get(v_a_2753_, 3);
v_defEqCtx_x3f_2825_ = lean_ctor_get(v_a_2753_, 4);
v_synthPendingDepth_2826_ = lean_ctor_get(v_a_2753_, 5);
v_canUnfold_x3f_2827_ = lean_ctor_get(v_a_2753_, 6);
v_univApprox_2828_ = lean_ctor_get_uint8(v_a_2753_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2829_ = lean_ctor_get_uint8(v_a_2753_, sizeof(void*)*7 + 2);
v_cacheInferType_2830_ = lean_ctor_get_uint8(v_a_2753_, sizeof(void*)*7 + 3);
if (v_isShared_2820_ == 0)
{
v_config_2832_ = v___x_2819_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 0, v_foApprox_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 1, v_ctxApprox_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 2, v_quasiPatternApprox_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 3, v_constApprox_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 4, v_isDefEqStuckEx_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 5, v_unificationHints_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 6, v_proofIrrelevance_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 7, v_assignSyntheticOpaque_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 8, v_offsetCnstrs_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 10, v_etaStruct_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 11, v_univApprox_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 12, v_iota_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 13, v_beta_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 14, v_proj_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 15, v_zeta_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 16, v_zetaDelta_2815_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 17, v_zetaUnused_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, 18, v_zetaHave_2817_);
v_config_2832_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
uint64_t v___x_2833_; uint64_t v___x_2834_; uint64_t v___x_2835_; uint64_t v___x_2836_; uint64_t v___x_2837_; uint64_t v_key_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v_beta_2842_; 
lean_ctor_set_uint8(v_config_2832_, 9, v___y_2798_);
v___x_2833_ = l_Lean_Meta_Context_configKey(v_a_2753_);
v___x_2834_ = 3ULL;
v___x_2835_ = lean_uint64_shift_right(v___x_2833_, v___x_2834_);
v___x_2836_ = lean_uint64_shift_left(v___x_2835_, v___x_2834_);
v___x_2837_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2798_);
v_key_2838_ = lean_uint64_lor(v___x_2836_, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2839_, 0, v_config_2832_);
lean_ctor_set_uint64(v___x_2839_, sizeof(void*)*1, v_key_2838_);
lean_inc(v_canUnfold_x3f_2827_);
lean_inc(v_synthPendingDepth_2826_);
lean_inc(v_defEqCtx_x3f_2825_);
lean_inc_ref(v_localInstances_2824_);
lean_inc_ref(v_lctx_2823_);
lean_inc(v_zetaDeltaSet_2822_);
v___x_2840_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v_zetaDeltaSet_2822_);
lean_ctor_set(v___x_2840_, 2, v_lctx_2823_);
lean_ctor_set(v___x_2840_, 3, v_localInstances_2824_);
lean_ctor_set(v___x_2840_, 4, v_defEqCtx_x3f_2825_);
lean_ctor_set(v___x_2840_, 5, v_synthPendingDepth_2826_);
lean_ctor_set(v___x_2840_, 6, v_canUnfold_x3f_2827_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*7, v_trackZetaDelta_2821_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*7 + 1, v_univApprox_2828_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2829_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*7 + 3, v_cacheInferType_2830_);
v___x_2841_ = l_Lean_Meta_Context_config(v___x_2840_);
v_beta_2842_ = lean_ctor_get_uint8(v___x_2841_, 13);
if (v_beta_2842_ == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v_iota_2843_; 
v_iota_2843_ = lean_ctor_get_uint8(v___x_2841_, 12);
if (v_iota_2843_ == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v_zeta_2844_; 
v_zeta_2844_ = lean_ctor_get_uint8(v___x_2841_, 15);
if (v_zeta_2844_ == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v_zetaHave_2845_; 
v_zetaHave_2845_ = lean_ctor_get_uint8(v___x_2841_, 18);
if (v_zetaHave_2845_ == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v_zetaDelta_2846_; 
v_zetaDelta_2846_ = lean_ctor_get_uint8(v___x_2841_, 16);
if (v_zetaDelta_2846_ == 0)
{
lean_dec_ref(v___x_2841_);
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v_etaStruct_2847_; uint8_t v_proj_2848_; uint8_t v___x_2849_; uint8_t v___x_2850_; 
v_etaStruct_2847_ = lean_ctor_get_uint8(v___x_2841_, 10);
v_proj_2848_ = lean_ctor_get_uint8(v___x_2841_, 14);
lean_dec_ref(v___x_2841_);
v___x_2849_ = 2;
v___x_2850_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
uint8_t v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = 0;
v___x_2852_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2847_, v___x_2851_);
if (v___x_2852_ == 0)
{
v___y_2759_ = v___x_2840_;
v___y_2760_ = v_inTypeClassResolution_2829_;
v___y_2761_ = v_univApprox_2828_;
v___y_2762_ = v_trackZetaDelta_2821_;
v___y_2763_ = v_defEqCtx_x3f_2825_;
v___y_2764_ = v_synthPendingDepth_2826_;
v___y_2765_ = v_lctx_2823_;
v___y_2766_ = v_cacheInferType_2830_;
v___y_2767_ = v_canUnfold_x3f_2827_;
v___y_2768_ = v_localInstances_2824_;
v___y_2769_ = v_zetaDeltaSet_2822_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2853_; 
lean_inc(v_a_2756_);
lean_inc_ref(v_a_2755_);
lean_inc(v_a_2754_);
v___x_2853_ = lean_apply_5(v_x_2752_, v___x_2840_, v_a_2754_, v_a_2755_, v_a_2756_, lean_box(0));
return v___x_2853_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2860_, lean_object* v_x_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2860_, v_x_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
return v_res_2867_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_box(0);
v___x_2869_ = l_Lean_interruptExceptionId;
v___x_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___closed__0);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b1_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b1_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b1_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v_ks_2890_; lean_object* v_vs_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2920_; 
v_ks_2890_ = lean_ctor_get(v_x_2886_, 0);
v_vs_2891_ = lean_ctor_get(v_x_2886_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_x_2886_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2893_ = v_x_2886_;
v_isShared_2894_ = v_isSharedCheck_2920_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_vs_2891_);
lean_inc(v_ks_2890_);
lean_dec(v_x_2886_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2920_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
uint8_t v___y_2896_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_array_get_size(v_ks_2890_);
v___x_2909_ = lean_nat_dec_lt(v_x_2887_, v___x_2908_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_del_object(v___x_2893_);
lean_dec(v_x_2887_);
v___x_2910_ = lean_array_push(v_ks_2890_, v_x_2888_);
v___x_2911_ = lean_array_push(v_vs_2891_, v_x_2889_);
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
return v___x_2912_;
}
else
{
lean_object* v_expr_2913_; uint64_t v_configKey_2914_; lean_object* v_k_x27_2915_; lean_object* v_expr_2916_; uint64_t v_configKey_2917_; uint8_t v___x_2918_; 
v_expr_2913_ = lean_ctor_get(v_x_2888_, 0);
v_configKey_2914_ = lean_ctor_get_uint64(v_x_2888_, sizeof(void*)*1);
v_k_x27_2915_ = lean_array_fget_borrowed(v_ks_2890_, v_x_2887_);
v_expr_2916_ = lean_ctor_get(v_k_x27_2915_, 0);
v_configKey_2917_ = lean_ctor_get_uint64(v_k_x27_2915_, sizeof(void*)*1);
v___x_2918_ = lean_expr_equal(v_expr_2913_, v_expr_2916_);
if (v___x_2918_ == 0)
{
v___y_2896_ = v___x_2918_;
goto v___jp_2895_;
}
else
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_uint64_dec_eq(v_configKey_2914_, v_configKey_2917_);
v___y_2896_ = v___x_2919_;
goto v___jp_2895_;
}
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
lean_object* v___x_2898_; 
if (v_isShared_2894_ == 0)
{
v___x_2898_ = v___x_2893_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_ks_2890_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_vs_2891_);
v___x_2898_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_unsigned_to_nat(1u);
v___x_2900_ = lean_nat_add(v_x_2887_, v___x_2899_);
lean_dec(v_x_2887_);
v_x_2886_ = v___x_2898_;
v_x_2887_ = v___x_2900_;
goto _start;
}
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2903_ = lean_array_fset(v_ks_2890_, v_x_2887_, v_x_2888_);
v___x_2904_ = lean_array_fset(v_vs_2891_, v_x_2887_, v_x_2889_);
lean_dec(v_x_2887_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 1, v___x_2904_);
lean_ctor_set(v___x_2893_, 0, v___x_2903_);
v___x_2906_ = v___x_2893_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2___redArg(lean_object* v_n_2921_, lean_object* v_k_2922_, lean_object* v_v_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4___redArg(v_n_2921_, v___x_2924_, v_k_2922_, v_v_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object* v_x_2927_, size_t v_x_2928_, size_t v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
lean_object* v_es_2932_; size_t v___x_2933_; size_t v___x_2934_; lean_object* v_j_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_es_2932_ = lean_ctor_get(v_x_2927_, 0);
v___x_2933_ = ((size_t)31ULL);
v___x_2934_ = lean_usize_land(v_x_2928_, v___x_2933_);
v_j_2935_ = lean_usize_to_nat(v___x_2934_);
v___x_2936_ = lean_array_get_size(v_es_2932_);
v___x_2937_ = lean_nat_dec_lt(v_j_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_dec(v_j_2935_);
lean_dec(v_x_2931_);
lean_dec_ref(v_x_2930_);
return v_x_2927_;
}
else
{
lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2983_; 
lean_inc_ref(v_es_2932_);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_x_2927_, 0);
lean_dec(v_unused_2984_);
v___x_2939_ = v_x_2927_;
v_isShared_2940_ = v_isSharedCheck_2983_;
goto v_resetjp_2938_;
}
else
{
lean_dec(v_x_2927_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2983_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_v_2941_; lean_object* v___x_2942_; lean_object* v_xs_x27_2943_; lean_object* v___y_2945_; 
v_v_2941_ = lean_array_fget(v_es_2932_, v_j_2935_);
v___x_2942_ = lean_box(0);
v_xs_x27_2943_ = lean_array_fset(v_es_2932_, v_j_2935_, v___x_2942_);
switch(lean_obj_tag(v_v_2941_))
{
case 0:
{
lean_object* v_key_2950_; lean_object* v_val_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2968_; 
v_key_2950_ = lean_ctor_get(v_v_2941_, 0);
v_val_2951_ = lean_ctor_get(v_v_2941_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_v_2941_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2953_ = v_v_2941_;
v_isShared_2954_ = v_isSharedCheck_2968_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_val_2951_);
lean_inc(v_key_2950_);
lean_dec(v_v_2941_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2968_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
uint8_t v___y_2956_; lean_object* v_expr_2962_; uint64_t v_configKey_2963_; lean_object* v_expr_2964_; uint64_t v_configKey_2965_; uint8_t v___x_2966_; 
v_expr_2962_ = lean_ctor_get(v_x_2930_, 0);
v_configKey_2963_ = lean_ctor_get_uint64(v_x_2930_, sizeof(void*)*1);
v_expr_2964_ = lean_ctor_get(v_key_2950_, 0);
v_configKey_2965_ = lean_ctor_get_uint64(v_key_2950_, sizeof(void*)*1);
v___x_2966_ = lean_expr_equal(v_expr_2962_, v_expr_2964_);
if (v___x_2966_ == 0)
{
v___y_2956_ = v___x_2966_;
goto v___jp_2955_;
}
else
{
uint8_t v___x_2967_; 
v___x_2967_ = lean_uint64_dec_eq(v_configKey_2963_, v_configKey_2965_);
v___y_2956_ = v___x_2967_;
goto v___jp_2955_;
}
v___jp_2955_:
{
if (v___y_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_del_object(v___x_2953_);
v___x_2957_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2950_, v_val_2951_, v_x_2930_, v_x_2931_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___y_2945_ = v___x_2958_;
goto v___jp_2944_;
}
else
{
lean_object* v___x_2960_; 
lean_dec(v_val_2951_);
lean_dec(v_key_2950_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v_x_2931_);
lean_ctor_set(v___x_2953_, 0, v_x_2930_);
v___x_2960_ = v___x_2953_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_x_2930_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_x_2931_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v___y_2945_ = v___x_2960_;
goto v___jp_2944_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2981_; 
v_node_2969_ = lean_ctor_get(v_v_2941_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_v_2941_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2971_ = v_v_2941_;
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_node_2969_);
lean_dec(v_v_2941_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2981_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
size_t v___x_2973_; size_t v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2973_ = ((size_t)5ULL);
v___x_2974_ = lean_usize_shift_right(v_x_2928_, v___x_2973_);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_x_2929_, v___x_2975_);
v___x_2977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_node_2969_, v___x_2974_, v___x_2976_, v_x_2930_, v_x_2931_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2977_);
v___x_2979_ = v___x_2971_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
v___y_2945_ = v___x_2979_;
goto v___jp_2944_;
}
}
}
default: 
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_x_2930_);
lean_ctor_set(v___x_2982_, 1, v_x_2931_);
v___y_2945_ = v___x_2982_;
goto v___jp_2944_;
}
}
v___jp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_array_fset(v_xs_x27_2943_, v_j_2935_, v___y_2945_);
lean_dec(v_j_2935_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2946_);
v___x_2948_ = v___x_2939_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
else
{
lean_object* v_ks_2985_; lean_object* v_vs_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3006_; 
v_ks_2985_ = lean_ctor_get(v_x_2927_, 0);
v_vs_2986_ = lean_ctor_get(v_x_2927_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2988_ = v_x_2927_;
v_isShared_2989_ = v_isSharedCheck_3006_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_vs_2986_);
lean_inc(v_ks_2985_);
lean_dec(v_x_2927_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3006_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_ks_2985_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_vs_2986_);
v___x_2991_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v_newNode_2992_; uint8_t v___y_2994_; size_t v___x_3000_; uint8_t v___x_3001_; 
v_newNode_2992_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2___redArg(v___x_2991_, v_x_2930_, v_x_2931_);
v___x_3000_ = ((size_t)7ULL);
v___x_3001_ = lean_usize_dec_le(v___x_3000_, v_x_2929_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2992_);
v___x_3003_ = lean_unsigned_to_nat(4u);
v___x_3004_ = lean_nat_dec_lt(v___x_3002_, v___x_3003_);
lean_dec(v___x_3002_);
v___y_2994_ = v___x_3004_;
goto v___jp_2993_;
}
else
{
v___y_2994_ = v___x_3001_;
goto v___jp_2993_;
}
v___jp_2993_:
{
if (v___y_2994_ == 0)
{
lean_object* v_ks_2995_; lean_object* v_vs_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_ks_2995_ = lean_ctor_get(v_newNode_2992_, 0);
lean_inc_ref(v_ks_2995_);
v_vs_2996_ = lean_ctor_get(v_newNode_2992_, 1);
lean_inc_ref(v_vs_2996_);
lean_dec_ref(v_newNode_2992_);
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___closed__0);
v___x_2999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg(v_x_2929_, v_ks_2995_, v_vs_2996_, v___x_2997_, v___x_2998_);
lean_dec_ref(v_vs_2996_);
lean_dec_ref(v_ks_2995_);
return v___x_2999_;
}
else
{
return v_newNode_2992_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg(size_t v_depth_3007_, lean_object* v_keys_3008_, lean_object* v_vals_3009_, lean_object* v_i_3010_, lean_object* v_entries_3011_){
_start:
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = lean_array_get_size(v_keys_3008_);
v___x_3013_ = lean_nat_dec_lt(v_i_3010_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec(v_i_3010_);
return v_entries_3011_;
}
else
{
lean_object* v_k_3014_; lean_object* v_expr_3015_; uint64_t v_configKey_3016_; lean_object* v_v_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; size_t v_h_3020_; size_t v___x_3021_; lean_object* v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; size_t v___x_3025_; size_t v_h_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_k_3014_ = lean_array_fget_borrowed(v_keys_3008_, v_i_3010_);
v_expr_3015_ = lean_ctor_get(v_k_3014_, 0);
v_configKey_3016_ = lean_ctor_get_uint64(v_k_3014_, sizeof(void*)*1);
v_v_3017_ = lean_array_fget_borrowed(v_vals_3009_, v_i_3010_);
v___x_3018_ = l_Lean_Expr_hash(v_expr_3015_);
v___x_3019_ = lean_uint64_mix_hash(v___x_3018_, v_configKey_3016_);
v_h_3020_ = lean_uint64_to_usize(v___x_3019_);
v___x_3021_ = ((size_t)5ULL);
v___x_3022_ = lean_unsigned_to_nat(1u);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_sub(v_depth_3007_, v___x_3023_);
v___x_3025_ = lean_usize_mul(v___x_3021_, v___x_3024_);
v_h_3026_ = lean_usize_shift_right(v_h_3020_, v___x_3025_);
v___x_3027_ = lean_nat_add(v_i_3010_, v___x_3022_);
lean_dec(v_i_3010_);
lean_inc(v_v_3017_);
lean_inc(v_k_3014_);
v___x_3028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_entries_3011_, v_h_3026_, v_depth_3007_, v_k_3014_, v_v_3017_);
v_i_3010_ = v___x_3027_;
v_entries_3011_ = v___x_3028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_3030_, lean_object* v_keys_3031_, lean_object* v_vals_3032_, lean_object* v_i_3033_, lean_object* v_entries_3034_){
_start:
{
size_t v_depth_boxed_3035_; lean_object* v_res_3036_; 
v_depth_boxed_3035_ = lean_unbox_usize(v_depth_3030_);
lean_dec(v_depth_3030_);
v_res_3036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg(v_depth_boxed_3035_, v_keys_3031_, v_vals_3032_, v_i_3033_, v_entries_3034_);
lean_dec_ref(v_vals_3032_);
lean_dec_ref(v_keys_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object* v_x_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
size_t v_x_2791__boxed_3042_; size_t v_x_2792__boxed_3043_; lean_object* v_res_3044_; 
v_x_2791__boxed_3042_ = lean_unbox_usize(v_x_3038_);
lean_dec(v_x_3038_);
v_x_2792__boxed_3043_ = lean_unbox_usize(v_x_3039_);
lean_dec(v_x_3039_);
v_res_3044_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3037_, v_x_2791__boxed_3042_, v_x_2792__boxed_3043_, v_x_3040_, v_x_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_expr_3048_; uint64_t v_configKey_3049_; uint64_t v___x_3050_; uint64_t v___x_3051_; size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v_expr_3048_ = lean_ctor_get(v_x_3046_, 0);
v_configKey_3049_ = lean_ctor_get_uint64(v_x_3046_, sizeof(void*)*1);
v___x_3050_ = l_Lean_Expr_hash(v_expr_3048_);
v___x_3051_ = lean_uint64_mix_hash(v___x_3050_, v_configKey_3049_);
v___x_3052_ = lean_uint64_to_usize(v___x_3051_);
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3045_, v___x_3052_, v___x_3053_, v_x_3046_, v_x_3047_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_3055_, lean_object* v_vals_3056_, lean_object* v_i_3057_, lean_object* v_k_3058_){
_start:
{
uint8_t v___y_3060_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_array_get_size(v_keys_3055_);
v___x_3067_ = lean_nat_dec_lt(v_i_3057_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
lean_dec(v_i_3057_);
v___x_3068_ = lean_box(0);
return v___x_3068_;
}
else
{
lean_object* v_expr_3069_; uint64_t v_configKey_3070_; lean_object* v_k_x27_3071_; lean_object* v_expr_3072_; uint64_t v_configKey_3073_; uint8_t v___x_3074_; 
v_expr_3069_ = lean_ctor_get(v_k_3058_, 0);
v_configKey_3070_ = lean_ctor_get_uint64(v_k_3058_, sizeof(void*)*1);
v_k_x27_3071_ = lean_array_fget_borrowed(v_keys_3055_, v_i_3057_);
v_expr_3072_ = lean_ctor_get(v_k_x27_3071_, 0);
v_configKey_3073_ = lean_ctor_get_uint64(v_k_x27_3071_, sizeof(void*)*1);
v___x_3074_ = lean_expr_equal(v_expr_3069_, v_expr_3072_);
if (v___x_3074_ == 0)
{
v___y_3060_ = v___x_3074_;
goto v___jp_3059_;
}
else
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_uint64_dec_eq(v_configKey_3070_, v_configKey_3073_);
v___y_3060_ = v___x_3075_;
goto v___jp_3059_;
}
}
v___jp_3059_:
{
if (v___y_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_add(v_i_3057_, v___x_3061_);
lean_dec(v_i_3057_);
v_i_3057_ = v___x_3062_;
goto _start;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_array_fget_borrowed(v_vals_3056_, v_i_3057_);
lean_dec(v_i_3057_);
lean_inc(v___x_3064_);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_3076_, lean_object* v_vals_3077_, lean_object* v_i_3078_, lean_object* v_k_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg(v_keys_3076_, v_vals_3077_, v_i_3078_, v_k_3079_);
lean_dec_ref(v_k_3079_);
lean_dec_ref(v_vals_3077_);
lean_dec_ref(v_keys_3076_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object* v_x_3081_, size_t v_x_3082_, lean_object* v_x_3083_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
lean_object* v_es_3084_; lean_object* v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; lean_object* v_j_3088_; lean_object* v___x_3089_; 
v_es_3084_ = lean_ctor_get(v_x_3081_, 0);
v___x_3085_ = lean_box(2);
v___x_3086_ = ((size_t)31ULL);
v___x_3087_ = lean_usize_land(v_x_3082_, v___x_3086_);
v_j_3088_ = lean_usize_to_nat(v___x_3087_);
v___x_3089_ = lean_array_get_borrowed(v___x_3085_, v_es_3084_, v_j_3088_);
lean_dec(v_j_3088_);
switch(lean_obj_tag(v___x_3089_))
{
case 0:
{
lean_object* v_key_3090_; lean_object* v_val_3091_; uint8_t v___y_3093_; lean_object* v_expr_3096_; uint64_t v_configKey_3097_; lean_object* v_expr_3098_; uint64_t v_configKey_3099_; uint8_t v___x_3100_; 
v_key_3090_ = lean_ctor_get(v___x_3089_, 0);
v_val_3091_ = lean_ctor_get(v___x_3089_, 1);
v_expr_3096_ = lean_ctor_get(v_x_3083_, 0);
v_configKey_3097_ = lean_ctor_get_uint64(v_x_3083_, sizeof(void*)*1);
v_expr_3098_ = lean_ctor_get(v_key_3090_, 0);
v_configKey_3099_ = lean_ctor_get_uint64(v_key_3090_, sizeof(void*)*1);
v___x_3100_ = lean_expr_equal(v_expr_3096_, v_expr_3098_);
if (v___x_3100_ == 0)
{
v___y_3093_ = v___x_3100_;
goto v___jp_3092_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_uint64_dec_eq(v_configKey_3097_, v_configKey_3099_);
v___y_3093_ = v___x_3101_;
goto v___jp_3092_;
}
v___jp_3092_:
{
if (v___y_3093_ == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_box(0);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; 
lean_inc(v_val_3091_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_val_3091_);
return v___x_3095_;
}
}
}
case 1:
{
lean_object* v_node_3102_; size_t v___x_3103_; size_t v___x_3104_; 
v_node_3102_ = lean_ctor_get(v___x_3089_, 0);
v___x_3103_ = ((size_t)5ULL);
v___x_3104_ = lean_usize_shift_right(v_x_3082_, v___x_3103_);
v_x_3081_ = v_node_3102_;
v_x_3082_ = v___x_3104_;
goto _start;
}
default: 
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_box(0);
return v___x_3106_;
}
}
}
else
{
lean_object* v_ks_3107_; lean_object* v_vs_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_ks_3107_ = lean_ctor_get(v_x_3081_, 0);
v_vs_3108_ = lean_ctor_get(v_x_3081_, 1);
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg(v_ks_3107_, v_vs_3108_, v___x_3109_, v_x_3083_);
return v___x_3110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_x_3113_){
_start:
{
size_t v_x_3000__boxed_3114_; lean_object* v_res_3115_; 
v_x_3000__boxed_3114_ = lean_unbox_usize(v_x_3112_);
lean_dec(v_x_3112_);
v_res_3115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3111_, v_x_3000__boxed_3114_, v_x_3113_);
lean_dec_ref(v_x_3113_);
lean_dec_ref(v_x_3111_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3116_, lean_object* v_x_3117_){
_start:
{
lean_object* v_expr_3118_; uint64_t v_configKey_3119_; uint64_t v___x_3120_; uint64_t v___x_3121_; size_t v___x_3122_; lean_object* v___x_3123_; 
v_expr_3118_ = lean_ctor_get(v_x_3117_, 0);
v_configKey_3119_ = lean_ctor_get_uint64(v_x_3117_, sizeof(void*)*1);
v___x_3120_ = l_Lean_Expr_hash(v_expr_3118_);
v___x_3121_ = lean_uint64_mix_hash(v___x_3120_, v_configKey_3119_);
v___x_3122_ = lean_uint64_to_usize(v___x_3121_);
v___x_3123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3116_, v___x_3122_, v_x_3117_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg___boxed(lean_object* v_x_3124_, lean_object* v_x_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3124_, v_x_3125_);
lean_dec_ref(v_x_3125_);
lean_dec_ref(v_x_3124_);
return v_res_3126_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___y_3137_; uint8_t v___y_3178_; lean_object* v___y_3228_; uint8_t v___y_3269_; 
switch(lean_obj_tag(v_e_3130_))
{
case 0:
{
lean_object* v_deBruijnIndex_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_deBruijnIndex_3318_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_deBruijnIndex_3318_);
lean_dec_ref_known(v_e_3130_, 1);
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3320_ = l_Lean_mkBVar(v_deBruijnIndex_3318_);
v___x_3321_ = l_Lean_MessageData_ofExpr(v___x_3320_);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3319_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3322_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3323_;
}
case 1:
{
lean_object* v_fvarId_3324_; lean_object* v___x_3325_; 
v_fvarId_3324_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_fvarId_3324_);
lean_dec_ref_known(v_e_3130_, 1);
v___x_3325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3324_, v_a_3131_, v_a_3133_, v_a_3134_);
return v___x_3325_;
}
case 2:
{
lean_object* v_mvarId_3326_; lean_object* v___x_3327_; 
v_mvarId_3326_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_mvarId_3326_);
lean_dec_ref_known(v_e_3130_, 1);
v___x_3327_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3326_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3327_;
}
case 3:
{
lean_object* v_u_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_u_3328_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_u_3328_);
lean_dec_ref_known(v_e_3130_, 1);
v___x_3329_ = l_Lean_Level_succ___override(v_u_3328_);
v___x_3330_ = l_Lean_mkSort(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
case 4:
{
lean_object* v_declName_3332_; lean_object* v_us_3333_; lean_object* v___y_3335_; uint8_t v___y_3376_; 
v_declName_3332_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_declName_3332_);
v_us_3333_ = lean_ctor_get(v_e_3130_, 1);
lean_inc(v_us_3333_);
if (lean_obj_tag(v_us_3333_) == 0)
{
lean_object* v___x_3425_; 
lean_dec_ref_known(v_e_3130_, 2);
v___x_3425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3332_, v_us_3333_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3425_;
}
else
{
uint8_t v_cacheInferType_3426_; uint8_t v___x_3427_; 
v_cacheInferType_3426_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
v___x_3427_ = lean_bool_not(v_cacheInferType_3426_);
if (v___x_3427_ == 0)
{
uint8_t v___x_3428_; 
v___x_3428_ = l_Lean_Expr_hasMVar(v_e_3130_);
v___y_3376_ = v___x_3428_;
goto v___jp_3375_;
}
else
{
v___y_3376_ = v___x_3427_;
goto v___jp_3375_;
}
}
v___jp_3334_:
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3332_, v_us_3333_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; uint8_t v___x_3338_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
v___x_3338_ = l_Lean_Expr_hasMVar(v_a_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3373_; 
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v___x_3336_, 0);
lean_dec(v_unused_3374_);
v___x_3340_ = v___x_3336_;
v_isShared_3341_ = v_isSharedCheck_3373_;
goto v_resetjp_3339_;
}
else
{
lean_dec(v___x_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3373_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_cache_3343_; lean_object* v_mctx_3344_; lean_object* v_zetaDeltaFVarIds_3345_; lean_object* v_postponed_3346_; lean_object* v_diag_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3372_; 
v___x_3342_ = lean_st_ref_take(v_a_3132_);
v_cache_3343_ = lean_ctor_get(v___x_3342_, 1);
v_mctx_3344_ = lean_ctor_get(v___x_3342_, 0);
v_zetaDeltaFVarIds_3345_ = lean_ctor_get(v___x_3342_, 2);
v_postponed_3346_ = lean_ctor_get(v___x_3342_, 3);
v_diag_3347_ = lean_ctor_get(v___x_3342_, 4);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3349_ = v___x_3342_;
v_isShared_3350_ = v_isSharedCheck_3372_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_diag_3347_);
lean_inc(v_postponed_3346_);
lean_inc(v_zetaDeltaFVarIds_3345_);
lean_inc(v_cache_3343_);
lean_inc(v_mctx_3344_);
lean_dec(v___x_3342_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3372_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_inferType_3351_; lean_object* v_funInfo_3352_; lean_object* v_synthInstance_3353_; lean_object* v_whnf_3354_; lean_object* v_defEqTrans_3355_; lean_object* v_defEqPerm_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3371_; 
v_inferType_3351_ = lean_ctor_get(v_cache_3343_, 0);
v_funInfo_3352_ = lean_ctor_get(v_cache_3343_, 1);
v_synthInstance_3353_ = lean_ctor_get(v_cache_3343_, 2);
v_whnf_3354_ = lean_ctor_get(v_cache_3343_, 3);
v_defEqTrans_3355_ = lean_ctor_get(v_cache_3343_, 4);
v_defEqPerm_3356_ = lean_ctor_get(v_cache_3343_, 5);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_cache_3343_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3358_ = v_cache_3343_;
v_isShared_3359_ = v_isSharedCheck_3371_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_defEqPerm_3356_);
lean_inc(v_defEqTrans_3355_);
lean_inc(v_whnf_3354_);
lean_inc(v_synthInstance_3353_);
lean_inc(v_funInfo_3352_);
lean_inc(v_inferType_3351_);
lean_dec(v_cache_3343_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3371_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_inc(v_a_3337_);
v___x_3360_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3351_, v___y_3335_, v_a_3337_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3362_ = v___x_3358_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_funInfo_3352_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_synthInstance_3353_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_whnf_3354_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_defEqTrans_3355_);
lean_ctor_set(v_reuseFailAlloc_3370_, 5, v_defEqPerm_3356_);
v___x_3362_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3364_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v___x_3362_);
v___x_3364_ = v___x_3349_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_mctx_3344_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_zetaDeltaFVarIds_3345_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_postponed_3346_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_diag_3347_);
v___x_3364_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3365_ = lean_st_ref_set(v_a_3132_, v___x_3364_);
if (v_isShared_3341_ == 0)
{
v___x_3367_ = v___x_3340_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3337_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3337_);
lean_dec_ref(v___y_3335_);
return v___x_3336_;
}
}
else
{
lean_dec_ref(v___y_3335_);
return v___x_3336_;
}
}
v___jp_3375_:
{
if (v___y_3376_ == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3402_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3402_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v_cache_3383_; lean_object* v_inferType_3384_; lean_object* v___x_3385_; 
v___x_3382_ = lean_st_ref_get(v_a_3132_);
v_cache_3383_ = lean_ctor_get(v___x_3382_, 1);
lean_inc_ref(v_cache_3383_);
lean_dec(v___x_3382_);
v_inferType_3384_ = lean_ctor_get(v_cache_3383_, 0);
lean_inc_ref(v_inferType_3384_);
lean_dec_ref(v_cache_3383_);
v___x_3385_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3384_, v_a_3378_);
lean_dec_ref(v_inferType_3384_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_cancelTk_x3f_3386_; 
lean_del_object(v___x_3380_);
v_cancelTk_x3f_3386_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3386_) == 1)
{
lean_object* v_val_3387_; uint8_t v___x_3388_; 
v_val_3387_ = lean_ctor_get(v_cancelTk_x3f_3386_, 0);
v___x_3388_ = l_IO_CancelToken_isSet(v_val_3387_);
if (v___x_3388_ == 0)
{
v___y_3335_ = v_a_3378_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3389_; lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_a_3378_);
lean_dec(v_us_3333_);
lean_dec(v_declName_3332_);
v___x_3389_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
v___y_3335_ = v_a_3378_;
goto v___jp_3334_;
}
}
else
{
lean_object* v_val_3398_; lean_object* v___x_3400_; 
lean_dec(v_a_3378_);
lean_dec(v_us_3333_);
lean_dec(v_declName_3332_);
v_val_3398_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v___x_3385_, 1);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_val_3398_);
v___x_3400_ = v___x_3380_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_val_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_us_3333_);
lean_dec(v_declName_3332_);
v_a_3403_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3377_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3377_);
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
lean_object* v_cancelTk_x3f_3411_; 
lean_dec_ref_known(v_e_3130_, 2);
v_cancelTk_x3f_3411_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3411_) == 1)
{
lean_object* v_val_3412_; uint8_t v___x_3413_; 
v_val_3412_ = lean_ctor_get(v_cancelTk_x3f_3411_, 0);
v___x_3413_ = l_IO_CancelToken_isSet(v_val_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3332_, v_us_3333_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3414_;
}
else
{
lean_object* v___x_3415_; lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_us_3333_);
lean_dec(v_declName_3332_);
v___x_3415_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3332_, v_us_3333_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3424_;
}
}
}
}
case 5:
{
lean_object* v_fn_3429_; uint8_t v_cacheInferType_3430_; lean_object* v_nargs_3431_; lean_object* v___x_3432_; lean_object* v_dummy_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___y_3439_; uint8_t v___y_3480_; uint8_t v___x_3529_; 
v_fn_3429_ = lean_ctor_get(v_e_3130_, 0);
v_cacheInferType_3430_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
v_nargs_3431_ = l_Lean_Expr_getAppNumArgs(v_e_3130_);
v___x_3432_ = l_Lean_Expr_getAppFn(v_fn_3429_);
v_dummy_3433_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3431_);
v___x_3434_ = lean_mk_array(v_nargs_3431_, v_dummy_3433_);
v___x_3435_ = lean_unsigned_to_nat(1u);
v___x_3436_ = lean_nat_sub(v_nargs_3431_, v___x_3435_);
lean_dec(v_nargs_3431_);
lean_inc_ref(v_e_3130_);
v___x_3437_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3130_, v___x_3434_, v___x_3436_);
v___x_3529_ = lean_bool_not(v_cacheInferType_3430_);
if (v___x_3529_ == 0)
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_Expr_hasMVar(v_e_3130_);
v___y_3480_ = v___x_3530_;
goto v___jp_3479_;
}
else
{
v___y_3480_ = v___x_3529_;
goto v___jp_3479_;
}
v___jp_3438_:
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3432_, v___x_3437_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec_ref(v___x_3437_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; uint8_t v___x_3442_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
v___x_3442_ = l_Lean_Expr_hasMVar(v_a_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3477_; 
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3440_, 0);
lean_dec(v_unused_3478_);
v___x_3444_ = v___x_3440_;
v_isShared_3445_ = v_isSharedCheck_3477_;
goto v_resetjp_3443_;
}
else
{
lean_dec(v___x_3440_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3477_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v_cache_3447_; lean_object* v_mctx_3448_; lean_object* v_zetaDeltaFVarIds_3449_; lean_object* v_postponed_3450_; lean_object* v_diag_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3476_; 
v___x_3446_ = lean_st_ref_take(v_a_3132_);
v_cache_3447_ = lean_ctor_get(v___x_3446_, 1);
v_mctx_3448_ = lean_ctor_get(v___x_3446_, 0);
v_zetaDeltaFVarIds_3449_ = lean_ctor_get(v___x_3446_, 2);
v_postponed_3450_ = lean_ctor_get(v___x_3446_, 3);
v_diag_3451_ = lean_ctor_get(v___x_3446_, 4);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3453_ = v___x_3446_;
v_isShared_3454_ = v_isSharedCheck_3476_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_diag_3451_);
lean_inc(v_postponed_3450_);
lean_inc(v_zetaDeltaFVarIds_3449_);
lean_inc(v_cache_3447_);
lean_inc(v_mctx_3448_);
lean_dec(v___x_3446_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3476_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v_inferType_3455_; lean_object* v_funInfo_3456_; lean_object* v_synthInstance_3457_; lean_object* v_whnf_3458_; lean_object* v_defEqTrans_3459_; lean_object* v_defEqPerm_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3475_; 
v_inferType_3455_ = lean_ctor_get(v_cache_3447_, 0);
v_funInfo_3456_ = lean_ctor_get(v_cache_3447_, 1);
v_synthInstance_3457_ = lean_ctor_get(v_cache_3447_, 2);
v_whnf_3458_ = lean_ctor_get(v_cache_3447_, 3);
v_defEqTrans_3459_ = lean_ctor_get(v_cache_3447_, 4);
v_defEqPerm_3460_ = lean_ctor_get(v_cache_3447_, 5);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_cache_3447_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3462_ = v_cache_3447_;
v_isShared_3463_ = v_isSharedCheck_3475_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_defEqPerm_3460_);
lean_inc(v_defEqTrans_3459_);
lean_inc(v_whnf_3458_);
lean_inc(v_synthInstance_3457_);
lean_inc(v_funInfo_3456_);
lean_inc(v_inferType_3455_);
lean_dec(v_cache_3447_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3475_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_inc(v_a_3441_);
v___x_3464_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3455_, v___y_3439_, v_a_3441_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v___x_3464_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_funInfo_3456_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_synthInstance_3457_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_whnf_3458_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_defEqTrans_3459_);
lean_ctor_set(v_reuseFailAlloc_3474_, 5, v_defEqPerm_3460_);
v___x_3466_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3466_);
v___x_3468_ = v___x_3453_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_mctx_3448_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_zetaDeltaFVarIds_3449_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_postponed_3450_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_diag_3451_);
v___x_3468_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = lean_st_ref_set(v_a_3132_, v___x_3468_);
if (v_isShared_3445_ == 0)
{
v___x_3471_ = v___x_3444_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3441_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3441_);
lean_dec_ref(v___y_3439_);
return v___x_3440_;
}
}
else
{
lean_dec_ref(v___y_3439_);
return v___x_3440_;
}
}
v___jp_3479_:
{
if (v___y_3480_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3506_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3506_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3506_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v_cache_3487_; lean_object* v_inferType_3488_; lean_object* v___x_3489_; 
v___x_3486_ = lean_st_ref_get(v_a_3132_);
v_cache_3487_ = lean_ctor_get(v___x_3486_, 1);
lean_inc_ref(v_cache_3487_);
lean_dec(v___x_3486_);
v_inferType_3488_ = lean_ctor_get(v_cache_3487_, 0);
lean_inc_ref(v_inferType_3488_);
lean_dec_ref(v_cache_3487_);
v___x_3489_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3488_, v_a_3482_);
lean_dec_ref(v_inferType_3488_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_cancelTk_x3f_3490_; 
lean_del_object(v___x_3484_);
v_cancelTk_x3f_3490_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3490_) == 1)
{
lean_object* v_val_3491_; uint8_t v___x_3492_; 
v_val_3491_ = lean_ctor_get(v_cancelTk_x3f_3490_, 0);
v___x_3492_ = l_IO_CancelToken_isSet(v_val_3491_);
if (v___x_3492_ == 0)
{
v___y_3439_ = v_a_3482_;
goto v___jp_3438_;
}
else
{
lean_object* v___x_3493_; lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3482_);
lean_dec_ref(v___x_3437_);
lean_dec_ref(v___x_3432_);
v___x_3493_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
v___y_3439_ = v_a_3482_;
goto v___jp_3438_;
}
}
else
{
lean_object* v_val_3502_; lean_object* v___x_3504_; 
lean_dec(v_a_3482_);
lean_dec_ref(v___x_3437_);
lean_dec_ref(v___x_3432_);
v_val_3502_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v___x_3489_, 1);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_val_3502_);
v___x_3504_ = v___x_3484_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_val_3502_);
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
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v___x_3437_);
lean_dec_ref(v___x_3432_);
v_a_3507_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3481_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3481_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_cancelTk_x3f_3515_; 
lean_dec_ref_known(v_e_3130_, 2);
v_cancelTk_x3f_3515_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3515_) == 1)
{
lean_object* v_val_3516_; uint8_t v___x_3517_; 
v_val_3516_ = lean_ctor_get(v_cancelTk_x3f_3515_, 0);
v___x_3517_ = l_IO_CancelToken_isSet(v_val_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3432_, v___x_3437_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec_ref(v___x_3437_);
return v___x_3518_;
}
else
{
lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v___x_3437_);
lean_dec_ref(v___x_3432_);
v___x_3519_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
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
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3432_, v___x_3437_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec_ref(v___x_3437_);
return v___x_3528_;
}
}
}
}
case 7:
{
uint8_t v_cacheInferType_3531_; uint8_t v___x_3532_; 
v_cacheInferType_3531_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
v___x_3532_ = lean_bool_not(v_cacheInferType_3531_);
if (v___x_3532_ == 0)
{
uint8_t v___x_3533_; 
v___x_3533_ = l_Lean_Expr_hasMVar(v_e_3130_);
v___y_3178_ = v___x_3533_;
goto v___jp_3177_;
}
else
{
v___y_3178_ = v___x_3532_;
goto v___jp_3177_;
}
}
case 9:
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3534_ = lean_ctor_get(v_e_3130_, 0);
lean_inc_ref(v_a_3534_);
lean_dec_ref_known(v_e_3130_, 1);
v___x_3535_ = l_Lean_Literal_type(v_a_3534_);
lean_dec_ref(v_a_3534_);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
case 10:
{
lean_object* v_expr_3537_; 
v_expr_3537_ = lean_ctor_get(v_e_3130_, 1);
lean_inc_ref(v_expr_3537_);
lean_dec_ref_known(v_e_3130_, 2);
v_e_3130_ = v_expr_3537_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3539_; lean_object* v_idx_3540_; lean_object* v_struct_3541_; lean_object* v___y_3543_; uint8_t v___y_3584_; uint8_t v_cacheInferType_3633_; uint8_t v___x_3634_; 
v_typeName_3539_ = lean_ctor_get(v_e_3130_, 0);
lean_inc(v_typeName_3539_);
v_idx_3540_ = lean_ctor_get(v_e_3130_, 1);
lean_inc(v_idx_3540_);
v_struct_3541_ = lean_ctor_get(v_e_3130_, 2);
lean_inc_ref(v_struct_3541_);
v_cacheInferType_3633_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
v___x_3634_ = lean_bool_not(v_cacheInferType_3633_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
v___x_3635_ = l_Lean_Expr_hasMVar(v_e_3130_);
v___y_3584_ = v___x_3635_;
goto v___jp_3583_;
}
else
{
v___y_3584_ = v___x_3634_;
goto v___jp_3583_;
}
v___jp_3542_:
{
lean_object* v___x_3544_; 
v___x_3544_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3539_, v_idx_3540_, v_struct_3541_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; uint8_t v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
v___x_3546_ = l_Lean_Expr_hasMVar(v_a_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3581_; 
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3544_, 0);
lean_dec(v_unused_3582_);
v___x_3548_ = v___x_3544_;
v_isShared_3549_ = v_isSharedCheck_3581_;
goto v_resetjp_3547_;
}
else
{
lean_dec(v___x_3544_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3581_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; lean_object* v_cache_3551_; lean_object* v_mctx_3552_; lean_object* v_zetaDeltaFVarIds_3553_; lean_object* v_postponed_3554_; lean_object* v_diag_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3580_; 
v___x_3550_ = lean_st_ref_take(v_a_3132_);
v_cache_3551_ = lean_ctor_get(v___x_3550_, 1);
v_mctx_3552_ = lean_ctor_get(v___x_3550_, 0);
v_zetaDeltaFVarIds_3553_ = lean_ctor_get(v___x_3550_, 2);
v_postponed_3554_ = lean_ctor_get(v___x_3550_, 3);
v_diag_3555_ = lean_ctor_get(v___x_3550_, 4);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3557_ = v___x_3550_;
v_isShared_3558_ = v_isSharedCheck_3580_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_diag_3555_);
lean_inc(v_postponed_3554_);
lean_inc(v_zetaDeltaFVarIds_3553_);
lean_inc(v_cache_3551_);
lean_inc(v_mctx_3552_);
lean_dec(v___x_3550_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3580_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_inferType_3559_; lean_object* v_funInfo_3560_; lean_object* v_synthInstance_3561_; lean_object* v_whnf_3562_; lean_object* v_defEqTrans_3563_; lean_object* v_defEqPerm_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3579_; 
v_inferType_3559_ = lean_ctor_get(v_cache_3551_, 0);
v_funInfo_3560_ = lean_ctor_get(v_cache_3551_, 1);
v_synthInstance_3561_ = lean_ctor_get(v_cache_3551_, 2);
v_whnf_3562_ = lean_ctor_get(v_cache_3551_, 3);
v_defEqTrans_3563_ = lean_ctor_get(v_cache_3551_, 4);
v_defEqPerm_3564_ = lean_ctor_get(v_cache_3551_, 5);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_cache_3551_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3566_ = v_cache_3551_;
v_isShared_3567_ = v_isSharedCheck_3579_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_defEqPerm_3564_);
lean_inc(v_defEqTrans_3563_);
lean_inc(v_whnf_3562_);
lean_inc(v_synthInstance_3561_);
lean_inc(v_funInfo_3560_);
lean_inc(v_inferType_3559_);
lean_dec(v_cache_3551_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3579_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
lean_inc(v_a_3545_);
v___x_3568_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3559_, v___y_3543_, v_a_3545_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3568_);
v___x_3570_ = v___x_3566_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_funInfo_3560_);
lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_synthInstance_3561_);
lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_whnf_3562_);
lean_ctor_set(v_reuseFailAlloc_3578_, 4, v_defEqTrans_3563_);
lean_ctor_set(v_reuseFailAlloc_3578_, 5, v_defEqPerm_3564_);
v___x_3570_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3572_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3570_);
v___x_3572_ = v___x_3557_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_mctx_3552_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_zetaDeltaFVarIds_3553_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_postponed_3554_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_diag_3555_);
v___x_3572_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3573_ = lean_st_ref_set(v_a_3132_, v___x_3572_);
if (v_isShared_3549_ == 0)
{
v___x_3575_ = v___x_3548_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3545_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3545_);
lean_dec_ref(v___y_3543_);
return v___x_3544_;
}
}
else
{
lean_dec_ref(v___y_3543_);
return v___x_3544_;
}
}
v___jp_3583_:
{
if (v___y_3584_ == 0)
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3610_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3610_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3610_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v_cache_3591_; lean_object* v_inferType_3592_; lean_object* v___x_3593_; 
v___x_3590_ = lean_st_ref_get(v_a_3132_);
v_cache_3591_ = lean_ctor_get(v___x_3590_, 1);
lean_inc_ref(v_cache_3591_);
lean_dec(v___x_3590_);
v_inferType_3592_ = lean_ctor_get(v_cache_3591_, 0);
lean_inc_ref(v_inferType_3592_);
lean_dec_ref(v_cache_3591_);
v___x_3593_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3592_, v_a_3586_);
lean_dec_ref(v_inferType_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_cancelTk_x3f_3594_; 
lean_del_object(v___x_3588_);
v_cancelTk_x3f_3594_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3594_) == 1)
{
lean_object* v_val_3595_; uint8_t v___x_3596_; 
v_val_3595_ = lean_ctor_get(v_cancelTk_x3f_3594_, 0);
v___x_3596_ = l_IO_CancelToken_isSet(v_val_3595_);
if (v___x_3596_ == 0)
{
v___y_3543_ = v_a_3586_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec(v_a_3586_);
lean_dec_ref(v_struct_3541_);
lean_dec(v_idx_3540_);
lean_dec(v_typeName_3539_);
v___x_3597_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
else
{
v___y_3543_ = v_a_3586_;
goto v___jp_3542_;
}
}
else
{
lean_object* v_val_3606_; lean_object* v___x_3608_; 
lean_dec(v_a_3586_);
lean_dec_ref(v_struct_3541_);
lean_dec(v_idx_3540_);
lean_dec(v_typeName_3539_);
v_val_3606_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_val_3606_);
lean_dec_ref_known(v___x_3593_, 1);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v_val_3606_);
v___x_3608_ = v___x_3588_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_val_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_struct_3541_);
lean_dec(v_idx_3540_);
lean_dec(v_typeName_3539_);
v_a_3611_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3585_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3585_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_object* v_cancelTk_x3f_3619_; 
lean_dec_ref_known(v_e_3130_, 3);
v_cancelTk_x3f_3619_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3619_) == 1)
{
lean_object* v_val_3620_; uint8_t v___x_3621_; 
v_val_3620_ = lean_ctor_get(v_cancelTk_x3f_3619_, 0);
v___x_3621_ = l_IO_CancelToken_isSet(v_val_3620_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3539_, v_idx_3540_, v_struct_3541_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3622_;
}
else
{
lean_object* v___x_3623_; lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_struct_3541_);
lean_dec(v_idx_3540_);
lean_dec(v_typeName_3539_);
v___x_3623_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v___x_3632_; 
v___x_3632_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3539_, v_idx_3540_, v_struct_3541_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3632_;
}
}
}
}
default: 
{
uint8_t v_cacheInferType_3636_; uint8_t v___x_3637_; 
v_cacheInferType_3636_ = lean_ctor_get_uint8(v_a_3131_, sizeof(void*)*7 + 3);
v___x_3637_ = lean_bool_not(v_cacheInferType_3636_);
if (v___x_3637_ == 0)
{
uint8_t v___x_3638_; 
v___x_3638_ = l_Lean_Expr_hasMVar(v_e_3130_);
v___y_3269_ = v___x_3638_;
goto v___jp_3268_;
}
else
{
v___y_3269_ = v___x_3637_;
goto v___jp_3268_;
}
}
}
v___jp_3136_:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; uint8_t v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
v___x_3140_ = l_Lean_Expr_hasMVar(v_a_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3175_; 
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_3138_, 0);
lean_dec(v_unused_3176_);
v___x_3142_ = v___x_3138_;
v_isShared_3143_ = v_isSharedCheck_3175_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3138_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3175_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v_cache_3145_; lean_object* v_mctx_3146_; lean_object* v_zetaDeltaFVarIds_3147_; lean_object* v_postponed_3148_; lean_object* v_diag_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3174_; 
v___x_3144_ = lean_st_ref_take(v_a_3132_);
v_cache_3145_ = lean_ctor_get(v___x_3144_, 1);
v_mctx_3146_ = lean_ctor_get(v___x_3144_, 0);
v_zetaDeltaFVarIds_3147_ = lean_ctor_get(v___x_3144_, 2);
v_postponed_3148_ = lean_ctor_get(v___x_3144_, 3);
v_diag_3149_ = lean_ctor_get(v___x_3144_, 4);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3151_ = v___x_3144_;
v_isShared_3152_ = v_isSharedCheck_3174_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_diag_3149_);
lean_inc(v_postponed_3148_);
lean_inc(v_zetaDeltaFVarIds_3147_);
lean_inc(v_cache_3145_);
lean_inc(v_mctx_3146_);
lean_dec(v___x_3144_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3174_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v_inferType_3153_; lean_object* v_funInfo_3154_; lean_object* v_synthInstance_3155_; lean_object* v_whnf_3156_; lean_object* v_defEqTrans_3157_; lean_object* v_defEqPerm_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3173_; 
v_inferType_3153_ = lean_ctor_get(v_cache_3145_, 0);
v_funInfo_3154_ = lean_ctor_get(v_cache_3145_, 1);
v_synthInstance_3155_ = lean_ctor_get(v_cache_3145_, 2);
v_whnf_3156_ = lean_ctor_get(v_cache_3145_, 3);
v_defEqTrans_3157_ = lean_ctor_get(v_cache_3145_, 4);
v_defEqPerm_3158_ = lean_ctor_get(v_cache_3145_, 5);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_cache_3145_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3160_ = v_cache_3145_;
v_isShared_3161_ = v_isSharedCheck_3173_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_defEqPerm_3158_);
lean_inc(v_defEqTrans_3157_);
lean_inc(v_whnf_3156_);
lean_inc(v_synthInstance_3155_);
lean_inc(v_funInfo_3154_);
lean_inc(v_inferType_3153_);
lean_dec(v_cache_3145_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3173_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_inc(v_a_3139_);
v___x_3162_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3153_, v___y_3137_, v_a_3139_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3162_);
v___x_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_funInfo_3154_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_synthInstance_3155_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_whnf_3156_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_defEqTrans_3157_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v_defEqPerm_3158_);
v___x_3164_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3164_);
v___x_3166_ = v___x_3151_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_mctx_3146_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_zetaDeltaFVarIds_3147_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_postponed_3148_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_diag_3149_);
v___x_3166_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = lean_st_ref_set(v_a_3132_, v___x_3166_);
if (v_isShared_3143_ == 0)
{
v___x_3169_ = v___x_3142_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3139_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3139_);
lean_dec_ref(v___y_3137_);
return v___x_3138_;
}
}
else
{
lean_dec_ref(v___y_3137_);
return v___x_3138_;
}
}
v___jp_3177_:
{
if (v___y_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_inc_ref(v_e_3130_);
v___x_3179_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3204_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3204_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3204_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v_cache_3185_; lean_object* v_inferType_3186_; lean_object* v___x_3187_; 
v___x_3184_ = lean_st_ref_get(v_a_3132_);
v_cache_3185_ = lean_ctor_get(v___x_3184_, 1);
lean_inc_ref(v_cache_3185_);
lean_dec(v___x_3184_);
v_inferType_3186_ = lean_ctor_get(v_cache_3185_, 0);
lean_inc_ref(v_inferType_3186_);
lean_dec_ref(v_cache_3185_);
v___x_3187_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3186_, v_a_3180_);
lean_dec_ref(v_inferType_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_cancelTk_x3f_3188_; 
lean_del_object(v___x_3182_);
v_cancelTk_x3f_3188_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3188_) == 1)
{
lean_object* v_val_3189_; uint8_t v___x_3190_; 
v_val_3189_ = lean_ctor_get(v_cancelTk_x3f_3188_, 0);
v___x_3190_ = l_IO_CancelToken_isSet(v_val_3189_);
if (v___x_3190_ == 0)
{
v___y_3137_ = v_a_3180_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3191_; lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_a_3180_);
lean_dec_ref(v_e_3130_);
v___x_3191_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
v___y_3137_ = v_a_3180_;
goto v___jp_3136_;
}
}
else
{
lean_object* v_val_3200_; lean_object* v___x_3202_; 
lean_dec(v_a_3180_);
lean_dec_ref(v_e_3130_);
v_val_3200_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v___x_3187_, 1);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v_val_3200_);
v___x_3202_ = v___x_3182_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_val_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v_e_3130_);
v_a_3205_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3179_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3179_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_cancelTk_x3f_3213_; 
v_cancelTk_x3f_3213_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3213_) == 1)
{
lean_object* v_val_3214_; uint8_t v___x_3215_; 
v_val_3214_ = lean_ctor_get(v_cancelTk_x3f_3213_, 0);
v___x_3215_ = l_IO_CancelToken_isSet(v_val_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v_e_3130_);
v___x_3217_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3226_;
}
}
}
v___jp_3227_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; uint8_t v___x_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
v___x_3231_ = l_Lean_Expr_hasMVar(v_a_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3266_; 
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3229_, 0);
lean_dec(v_unused_3267_);
v___x_3233_ = v___x_3229_;
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3229_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3266_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v_cache_3236_; lean_object* v_mctx_3237_; lean_object* v_zetaDeltaFVarIds_3238_; lean_object* v_postponed_3239_; lean_object* v_diag_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3265_; 
v___x_3235_ = lean_st_ref_take(v_a_3132_);
v_cache_3236_ = lean_ctor_get(v___x_3235_, 1);
v_mctx_3237_ = lean_ctor_get(v___x_3235_, 0);
v_zetaDeltaFVarIds_3238_ = lean_ctor_get(v___x_3235_, 2);
v_postponed_3239_ = lean_ctor_get(v___x_3235_, 3);
v_diag_3240_ = lean_ctor_get(v___x_3235_, 4);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3242_ = v___x_3235_;
v_isShared_3243_ = v_isSharedCheck_3265_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_diag_3240_);
lean_inc(v_postponed_3239_);
lean_inc(v_zetaDeltaFVarIds_3238_);
lean_inc(v_cache_3236_);
lean_inc(v_mctx_3237_);
lean_dec(v___x_3235_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3265_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_inferType_3244_; lean_object* v_funInfo_3245_; lean_object* v_synthInstance_3246_; lean_object* v_whnf_3247_; lean_object* v_defEqTrans_3248_; lean_object* v_defEqPerm_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3264_; 
v_inferType_3244_ = lean_ctor_get(v_cache_3236_, 0);
v_funInfo_3245_ = lean_ctor_get(v_cache_3236_, 1);
v_synthInstance_3246_ = lean_ctor_get(v_cache_3236_, 2);
v_whnf_3247_ = lean_ctor_get(v_cache_3236_, 3);
v_defEqTrans_3248_ = lean_ctor_get(v_cache_3236_, 4);
v_defEqPerm_3249_ = lean_ctor_get(v_cache_3236_, 5);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_cache_3236_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3251_ = v_cache_3236_;
v_isShared_3252_ = v_isSharedCheck_3264_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_defEqPerm_3249_);
lean_inc(v_defEqTrans_3248_);
lean_inc(v_whnf_3247_);
lean_inc(v_synthInstance_3246_);
lean_inc(v_funInfo_3245_);
lean_inc(v_inferType_3244_);
lean_dec(v_cache_3236_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3264_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_inc(v_a_3230_);
v___x_3253_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3244_, v___y_3228_, v_a_3230_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_funInfo_3245_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_synthInstance_3246_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_whnf_3247_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_defEqTrans_3248_);
lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_defEqPerm_3249_);
v___x_3255_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v___x_3255_);
v___x_3257_ = v___x_3242_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_mctx_3237_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_zetaDeltaFVarIds_3238_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_postponed_3239_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v_diag_3240_);
v___x_3257_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_st_ref_set(v_a_3132_, v___x_3257_);
if (v_isShared_3234_ == 0)
{
v___x_3260_ = v___x_3233_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3230_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3230_);
lean_dec_ref(v___y_3228_);
return v___x_3229_;
}
}
else
{
lean_dec_ref(v___y_3228_);
return v___x_3229_;
}
}
v___jp_3268_:
{
if (v___y_3269_ == 0)
{
lean_object* v___x_3270_; 
lean_inc_ref(v_e_3130_);
v___x_3270_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3295_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v_cache_3276_; lean_object* v_inferType_3277_; lean_object* v___x_3278_; 
v___x_3275_ = lean_st_ref_get(v_a_3132_);
v_cache_3276_ = lean_ctor_get(v___x_3275_, 1);
lean_inc_ref(v_cache_3276_);
lean_dec(v___x_3275_);
v_inferType_3277_ = lean_ctor_get(v_cache_3276_, 0);
lean_inc_ref(v_inferType_3277_);
lean_dec_ref(v_cache_3276_);
v___x_3278_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3277_, v_a_3271_);
lean_dec_ref(v_inferType_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_cancelTk_x3f_3279_; 
lean_del_object(v___x_3273_);
v_cancelTk_x3f_3279_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3279_) == 1)
{
lean_object* v_val_3280_; uint8_t v___x_3281_; 
v_val_3280_ = lean_ctor_get(v_cancelTk_x3f_3279_, 0);
v___x_3281_ = l_IO_CancelToken_isSet(v_val_3280_);
if (v___x_3281_ == 0)
{
v___y_3228_ = v_a_3271_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3282_; lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_a_3271_);
lean_dec_ref(v_e_3130_);
v___x_3282_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
v___y_3228_ = v_a_3271_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_val_3291_; lean_object* v___x_3293_; 
lean_dec(v_a_3271_);
lean_dec_ref(v_e_3130_);
v_val_3291_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v___x_3278_, 1);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v_val_3291_);
v___x_3293_ = v___x_3273_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_val_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_e_3130_);
v_a_3296_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3270_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3270_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_cancelTk_x3f_3304_; 
v_cancelTk_x3f_3304_ = lean_ctor_get(v_a_3133_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3304_) == 1)
{
lean_object* v_val_3305_; uint8_t v___x_3306_; 
v_val_3305_ = lean_ctor_get(v_cancelTk_x3f_3304_, 0);
v___x_3306_ = l_IO_CancelToken_isSet(v_val_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_e_3130_);
v___x_3308_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg();
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b2_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_3647_, v_x_3648_, v_x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3651_, lean_object* v_x_3652_, lean_object* v_x_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3652_, v_x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_x_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(v_00_u03b2_3655_, v_x_3656_, v_x_3657_);
lean_dec_ref(v_x_3657_);
lean_dec_ref(v_x_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object* v_00_u03b2_3659_, lean_object* v_x_3660_, size_t v_x_3661_, size_t v_x_3662_, lean_object* v_x_3663_, lean_object* v_x_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3660_, v_x_3661_, v_x_3662_, v_x_3663_, v_x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
size_t v_x_4068__boxed_3672_; size_t v_x_4069__boxed_3673_; lean_object* v_res_3674_; 
v_x_4068__boxed_3672_ = lean_unbox_usize(v_x_3668_);
lean_dec(v_x_3668_);
v_x_4069__boxed_3673_ = lean_unbox_usize(v_x_3669_);
lean_dec(v_x_3669_);
v_res_3674_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(v_00_u03b2_3666_, v_x_3667_, v_x_4068__boxed_3672_, v_x_4069__boxed_3673_, v_x_3670_, v_x_3671_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object* v_00_u03b2_3675_, lean_object* v_x_3676_, size_t v_x_3677_, lean_object* v_x_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3676_, v_x_3677_, v_x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_){
_start:
{
size_t v_x_4085__boxed_3684_; lean_object* v_res_3685_; 
v_x_4085__boxed_3684_ = lean_unbox_usize(v_x_3682_);
lean_dec(v_x_3682_);
v_res_3685_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(v_00_u03b2_3680_, v_x_3681_, v_x_4085__boxed_3684_, v_x_3683_);
lean_dec_ref(v_x_3683_);
lean_dec_ref(v_x_3681_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3686_, lean_object* v_n_3687_, lean_object* v_k_3688_, lean_object* v_v_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2___redArg(v_n_3687_, v_k_3688_, v_v_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_3691_, size_t v_depth_3692_, lean_object* v_keys_3693_, lean_object* v_vals_3694_, lean_object* v_heq_3695_, lean_object* v_i_3696_, lean_object* v_entries_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___redArg(v_depth_3692_, v_keys_3693_, v_vals_3694_, v_i_3696_, v_entries_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_depth_3700_, lean_object* v_keys_3701_, lean_object* v_vals_3702_, lean_object* v_heq_3703_, lean_object* v_i_3704_, lean_object* v_entries_3705_){
_start:
{
size_t v_depth_boxed_3706_; lean_object* v_res_3707_; 
v_depth_boxed_3706_ = lean_unbox_usize(v_depth_3700_);
lean_dec(v_depth_3700_);
v_res_3707_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__3(v_00_u03b2_3699_, v_depth_boxed_3706_, v_keys_3701_, v_vals_3702_, v_heq_3703_, v_i_3704_, v_entries_3705_);
lean_dec_ref(v_vals_3702_);
lean_dec_ref(v_keys_3701_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_3708_, lean_object* v_keys_3709_, lean_object* v_vals_3710_, lean_object* v_heq_3711_, lean_object* v_i_3712_, lean_object* v_k_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___redArg(v_keys_3709_, v_vals_3710_, v_i_3712_, v_k_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_3715_, lean_object* v_keys_3716_, lean_object* v_vals_3717_, lean_object* v_heq_3718_, lean_object* v_i_3719_, lean_object* v_k_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__6(v_00_u03b2_3715_, v_keys_3716_, v_vals_3717_, v_heq_3718_, v_i_3719_, v_k_3720_);
lean_dec_ref(v_k_3720_);
lean_dec_ref(v_vals_3717_);
lean_dec_ref(v_keys_3716_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_3722_, lean_object* v_x_3723_, lean_object* v_x_3724_, lean_object* v_x_3725_, lean_object* v_x_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__2_spec__4___redArg(v_x_3723_, v_x_3724_, v_x_3725_, v_x_3726_);
return v___x_3727_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = l_Lean_maxRecDepthErrorMessage;
v___x_3734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3736_ = l_Lean_MessageData_ofFormat(v___x_3735_);
return v___x_3736_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3738_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3739_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___x_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3740_){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v_ref_3740_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3748_, lean_object* v_ref_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3749_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_ref_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3756_, v_ref_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; uint8_t v___y_3774_; uint8_t v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; uint8_t v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; uint8_t v___y_3782_; lean_object* v___y_3811_; uint8_t v___y_3812_; lean_object* v_fileName_3883_; lean_object* v_fileMap_3884_; lean_object* v_options_3885_; lean_object* v_currRecDepth_3886_; lean_object* v_maxRecDepth_3887_; lean_object* v_ref_3888_; lean_object* v_currNamespace_3889_; lean_object* v_openDecls_3890_; lean_object* v_initHeartbeats_3891_; lean_object* v_maxHeartbeats_3892_; lean_object* v_quotContext_3893_; lean_object* v_currMacroScope_3894_; uint8_t v_diag_3895_; lean_object* v_cancelTk_x3f_3896_; uint8_t v_suppressElabErrors_3897_; lean_object* v_inheritedTraceOptions_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3918_; 
v_fileName_3883_ = lean_ctor_get(v_a_3767_, 0);
v_fileMap_3884_ = lean_ctor_get(v_a_3767_, 1);
v_options_3885_ = lean_ctor_get(v_a_3767_, 2);
v_currRecDepth_3886_ = lean_ctor_get(v_a_3767_, 3);
v_maxRecDepth_3887_ = lean_ctor_get(v_a_3767_, 4);
v_ref_3888_ = lean_ctor_get(v_a_3767_, 5);
v_currNamespace_3889_ = lean_ctor_get(v_a_3767_, 6);
v_openDecls_3890_ = lean_ctor_get(v_a_3767_, 7);
v_initHeartbeats_3891_ = lean_ctor_get(v_a_3767_, 8);
v_maxHeartbeats_3892_ = lean_ctor_get(v_a_3767_, 9);
v_quotContext_3893_ = lean_ctor_get(v_a_3767_, 10);
v_currMacroScope_3894_ = lean_ctor_get(v_a_3767_, 11);
v_diag_3895_ = lean_ctor_get_uint8(v_a_3767_, sizeof(void*)*14);
v_cancelTk_x3f_3896_ = lean_ctor_get(v_a_3767_, 12);
v_suppressElabErrors_3897_ = lean_ctor_get_uint8(v_a_3767_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3898_ = lean_ctor_get(v_a_3767_, 13);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_a_3767_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3900_ = v_a_3767_;
v_isShared_3901_ = v_isSharedCheck_3918_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_inheritedTraceOptions_3898_);
lean_inc(v_cancelTk_x3f_3896_);
lean_inc(v_currMacroScope_3894_);
lean_inc(v_quotContext_3893_);
lean_inc(v_maxHeartbeats_3892_);
lean_inc(v_initHeartbeats_3891_);
lean_inc(v_openDecls_3890_);
lean_inc(v_currNamespace_3889_);
lean_inc(v_ref_3888_);
lean_inc(v_maxRecDepth_3887_);
lean_inc(v_currRecDepth_3886_);
lean_inc(v_options_3885_);
lean_inc(v_fileMap_3884_);
lean_inc(v_fileName_3883_);
lean_dec(v_a_3767_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3918_;
goto v_resetjp_3899_;
}
v___jp_3770_:
{
lean_object* v___x_3783_; uint8_t v_foApprox_3784_; uint8_t v_ctxApprox_3785_; uint8_t v_quasiPatternApprox_3786_; uint8_t v_constApprox_3787_; uint8_t v_isDefEqStuckEx_3788_; uint8_t v_unificationHints_3789_; uint8_t v_proofIrrelevance_3790_; uint8_t v_assignSyntheticOpaque_3791_; uint8_t v_offsetCnstrs_3792_; uint8_t v_transparency_3793_; uint8_t v_univApprox_3794_; uint8_t v_zetaUnused_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3809_; 
v___x_3783_ = l_Lean_Meta_Context_config(v___y_3772_);
lean_dec_ref(v___y_3772_);
v_foApprox_3784_ = lean_ctor_get_uint8(v___x_3783_, 0);
v_ctxApprox_3785_ = lean_ctor_get_uint8(v___x_3783_, 1);
v_quasiPatternApprox_3786_ = lean_ctor_get_uint8(v___x_3783_, 2);
v_constApprox_3787_ = lean_ctor_get_uint8(v___x_3783_, 3);
v_isDefEqStuckEx_3788_ = lean_ctor_get_uint8(v___x_3783_, 4);
v_unificationHints_3789_ = lean_ctor_get_uint8(v___x_3783_, 5);
v_proofIrrelevance_3790_ = lean_ctor_get_uint8(v___x_3783_, 6);
v_assignSyntheticOpaque_3791_ = lean_ctor_get_uint8(v___x_3783_, 7);
v_offsetCnstrs_3792_ = lean_ctor_get_uint8(v___x_3783_, 8);
v_transparency_3793_ = lean_ctor_get_uint8(v___x_3783_, 9);
v_univApprox_3794_ = lean_ctor_get_uint8(v___x_3783_, 11);
v_zetaUnused_3795_ = lean_ctor_get_uint8(v___x_3783_, 17);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3797_ = v___x_3783_;
v_isShared_3798_ = v_isSharedCheck_3809_;
goto v_resetjp_3796_;
}
else
{
lean_dec(v___x_3783_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3809_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
uint8_t v___x_3799_; uint8_t v___x_3800_; uint8_t v___x_3801_; lean_object* v___x_3803_; 
v___x_3799_ = 1;
v___x_3800_ = 0;
v___x_3801_ = 2;
if (v_isShared_3798_ == 0)
{
v___x_3803_ = v___x_3797_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 0, v_foApprox_3784_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 1, v_ctxApprox_3785_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 2, v_quasiPatternApprox_3786_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 3, v_constApprox_3787_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 4, v_isDefEqStuckEx_3788_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 5, v_unificationHints_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 6, v_proofIrrelevance_3790_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 7, v_assignSyntheticOpaque_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 8, v_offsetCnstrs_3792_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 9, v_transparency_3793_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 11, v_univApprox_3794_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, 17, v_zetaUnused_3795_);
v___x_3803_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
uint64_t v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_ctor_set_uint8(v___x_3803_, 10, v___x_3800_);
lean_ctor_set_uint8(v___x_3803_, 12, v___x_3799_);
lean_ctor_set_uint8(v___x_3803_, 13, v___x_3799_);
lean_ctor_set_uint8(v___x_3803_, 14, v___x_3801_);
lean_ctor_set_uint8(v___x_3803_, 15, v___x_3799_);
lean_ctor_set_uint8(v___x_3803_, 16, v___x_3799_);
lean_ctor_set_uint8(v___x_3803_, 18, v___x_3799_);
v___x_3804_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3803_);
v___x_3805_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set_uint64(v___x_3805_, sizeof(void*)*1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___y_3777_);
lean_ctor_set(v___x_3806_, 2, v___y_3779_);
lean_ctor_set(v___x_3806_, 3, v___y_3776_);
lean_ctor_set(v___x_3806_, 4, v___y_3771_);
lean_ctor_set(v___x_3806_, 5, v___y_3781_);
lean_ctor_set(v___x_3806_, 6, v___y_3780_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*7, v___y_3775_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*7 + 1, v___y_3774_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*7 + 2, v___y_3782_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*7 + 3, v___y_3778_);
v___x_3807_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3764_, v___x_3806_, v_a_3766_, v___y_3773_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v___y_3773_);
lean_dec(v_a_3766_);
lean_dec_ref_known(v___x_3806_, 7);
return v___x_3807_;
}
}
}
v___jp_3810_:
{
lean_object* v___x_3813_; uint8_t v_foApprox_3814_; uint8_t v_ctxApprox_3815_; uint8_t v_quasiPatternApprox_3816_; uint8_t v_constApprox_3817_; uint8_t v_isDefEqStuckEx_3818_; uint8_t v_unificationHints_3819_; uint8_t v_proofIrrelevance_3820_; uint8_t v_assignSyntheticOpaque_3821_; uint8_t v_offsetCnstrs_3822_; uint8_t v_etaStruct_3823_; uint8_t v_univApprox_3824_; uint8_t v_iota_3825_; uint8_t v_beta_3826_; uint8_t v_proj_3827_; uint8_t v_zeta_3828_; uint8_t v_zetaDelta_3829_; uint8_t v_zetaUnused_3830_; uint8_t v_zetaHave_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3882_; 
v___x_3813_ = l_Lean_Meta_Context_config(v_a_3765_);
v_foApprox_3814_ = lean_ctor_get_uint8(v___x_3813_, 0);
v_ctxApprox_3815_ = lean_ctor_get_uint8(v___x_3813_, 1);
v_quasiPatternApprox_3816_ = lean_ctor_get_uint8(v___x_3813_, 2);
v_constApprox_3817_ = lean_ctor_get_uint8(v___x_3813_, 3);
v_isDefEqStuckEx_3818_ = lean_ctor_get_uint8(v___x_3813_, 4);
v_unificationHints_3819_ = lean_ctor_get_uint8(v___x_3813_, 5);
v_proofIrrelevance_3820_ = lean_ctor_get_uint8(v___x_3813_, 6);
v_assignSyntheticOpaque_3821_ = lean_ctor_get_uint8(v___x_3813_, 7);
v_offsetCnstrs_3822_ = lean_ctor_get_uint8(v___x_3813_, 8);
v_etaStruct_3823_ = lean_ctor_get_uint8(v___x_3813_, 10);
v_univApprox_3824_ = lean_ctor_get_uint8(v___x_3813_, 11);
v_iota_3825_ = lean_ctor_get_uint8(v___x_3813_, 12);
v_beta_3826_ = lean_ctor_get_uint8(v___x_3813_, 13);
v_proj_3827_ = lean_ctor_get_uint8(v___x_3813_, 14);
v_zeta_3828_ = lean_ctor_get_uint8(v___x_3813_, 15);
v_zetaDelta_3829_ = lean_ctor_get_uint8(v___x_3813_, 16);
v_zetaUnused_3830_ = lean_ctor_get_uint8(v___x_3813_, 17);
v_zetaHave_3831_ = lean_ctor_get_uint8(v___x_3813_, 18);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3833_ = v___x_3813_;
v_isShared_3834_ = v_isSharedCheck_3882_;
goto v_resetjp_3832_;
}
else
{
lean_dec(v___x_3813_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3882_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
uint8_t v_trackZetaDelta_3835_; lean_object* v_zetaDeltaSet_3836_; lean_object* v_lctx_3837_; lean_object* v_localInstances_3838_; lean_object* v_defEqCtx_x3f_3839_; lean_object* v_synthPendingDepth_3840_; lean_object* v_canUnfold_x3f_3841_; uint8_t v_univApprox_3842_; uint8_t v_inTypeClassResolution_3843_; uint8_t v_cacheInferType_3844_; lean_object* v_config_3846_; 
v_trackZetaDelta_3835_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7);
v_zetaDeltaSet_3836_ = lean_ctor_get(v_a_3765_, 1);
lean_inc(v_zetaDeltaSet_3836_);
v_lctx_3837_ = lean_ctor_get(v_a_3765_, 2);
lean_inc_ref(v_lctx_3837_);
v_localInstances_3838_ = lean_ctor_get(v_a_3765_, 3);
lean_inc_ref(v_localInstances_3838_);
v_defEqCtx_x3f_3839_ = lean_ctor_get(v_a_3765_, 4);
lean_inc(v_defEqCtx_x3f_3839_);
v_synthPendingDepth_3840_ = lean_ctor_get(v_a_3765_, 5);
lean_inc(v_synthPendingDepth_3840_);
v_canUnfold_x3f_3841_ = lean_ctor_get(v_a_3765_, 6);
lean_inc(v_canUnfold_x3f_3841_);
v_univApprox_3842_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3843_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 2);
v_cacheInferType_3844_ = lean_ctor_get_uint8(v_a_3765_, sizeof(void*)*7 + 3);
if (v_isShared_3834_ == 0)
{
v_config_3846_ = v___x_3833_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 0, v_foApprox_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 1, v_ctxApprox_3815_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 2, v_quasiPatternApprox_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 3, v_constApprox_3817_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 4, v_isDefEqStuckEx_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 5, v_unificationHints_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 6, v_proofIrrelevance_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 7, v_assignSyntheticOpaque_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 8, v_offsetCnstrs_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 10, v_etaStruct_3823_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 11, v_univApprox_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 12, v_iota_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 13, v_beta_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 14, v_proj_3827_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 15, v_zeta_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 16, v_zetaDelta_3829_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 17, v_zetaUnused_3830_);
lean_ctor_set_uint8(v_reuseFailAlloc_3881_, 18, v_zetaHave_3831_);
v_config_3846_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
uint64_t v___x_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3873_; 
lean_ctor_set_uint8(v_config_3846_, 9, v___y_3812_);
v___x_3847_ = l_Lean_Meta_Context_configKey(v_a_3765_);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3874_ = lean_ctor_get(v_a_3765_, 6);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_a_3765_, 5);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_a_3765_, 4);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_a_3765_, 3);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_a_3765_, 2);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_a_3765_, 1);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_a_3765_, 0);
lean_dec(v_unused_3880_);
v___x_3849_ = v_a_3765_;
v_isShared_3850_ = v_isSharedCheck_3873_;
goto v_resetjp_3848_;
}
else
{
lean_dec(v_a_3765_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3873_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
uint64_t v___x_3851_; uint64_t v___x_3852_; uint64_t v___x_3853_; uint64_t v___x_3854_; uint64_t v_key_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3851_ = 3ULL;
v___x_3852_ = lean_uint64_shift_right(v___x_3847_, v___x_3851_);
v___x_3853_ = lean_uint64_shift_left(v___x_3852_, v___x_3851_);
v___x_3854_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3812_);
v_key_3855_ = lean_uint64_lor(v___x_3853_, v___x_3854_);
v___x_3856_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3856_, 0, v_config_3846_);
lean_ctor_set_uint64(v___x_3856_, sizeof(void*)*1, v_key_3855_);
lean_inc(v_canUnfold_x3f_3841_);
lean_inc(v_synthPendingDepth_3840_);
lean_inc(v_defEqCtx_x3f_3839_);
lean_inc_ref(v_localInstances_3838_);
lean_inc_ref(v_lctx_3837_);
lean_inc(v_zetaDeltaSet_3836_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3856_);
v___x_3858_ = v___x_3849_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_zetaDeltaSet_3836_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_lctx_3837_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_localInstances_3838_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_defEqCtx_x3f_3839_);
lean_ctor_set(v_reuseFailAlloc_3872_, 5, v_synthPendingDepth_3840_);
lean_ctor_set(v_reuseFailAlloc_3872_, 6, v_canUnfold_x3f_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3872_, sizeof(void*)*7, v_trackZetaDelta_3835_);
lean_ctor_set_uint8(v_reuseFailAlloc_3872_, sizeof(void*)*7 + 1, v_univApprox_3842_);
lean_ctor_set_uint8(v_reuseFailAlloc_3872_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3872_, sizeof(void*)*7 + 3, v_cacheInferType_3844_);
v___x_3858_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; uint8_t v_beta_3860_; 
v___x_3859_ = l_Lean_Meta_Context_config(v___x_3858_);
v_beta_3860_ = lean_ctor_get_uint8(v___x_3859_, 13);
if (v_beta_3860_ == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v_iota_3861_; 
v_iota_3861_ = lean_ctor_get_uint8(v___x_3859_, 12);
if (v_iota_3861_ == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v_zeta_3862_; 
v_zeta_3862_ = lean_ctor_get_uint8(v___x_3859_, 15);
if (v_zeta_3862_ == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v_zetaHave_3863_; 
v_zetaHave_3863_ = lean_ctor_get_uint8(v___x_3859_, 18);
if (v_zetaHave_3863_ == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v_zetaDelta_3864_; 
v_zetaDelta_3864_ = lean_ctor_get_uint8(v___x_3859_, 16);
if (v_zetaDelta_3864_ == 0)
{
lean_dec_ref(v___x_3859_);
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v_etaStruct_3865_; uint8_t v_proj_3866_; uint8_t v___x_3867_; uint8_t v___x_3868_; 
v_etaStruct_3865_ = lean_ctor_get_uint8(v___x_3859_, 10);
v_proj_3866_ = lean_ctor_get_uint8(v___x_3859_, 14);
lean_dec_ref(v___x_3859_);
v___x_3867_ = 2;
v___x_3868_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
uint8_t v___x_3869_; uint8_t v___x_3870_; 
v___x_3869_ = 0;
v___x_3870_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3865_, v___x_3869_);
if (v___x_3870_ == 0)
{
v___y_3771_ = v_defEqCtx_x3f_3839_;
v___y_3772_ = v___x_3858_;
v___y_3773_ = v___y_3811_;
v___y_3774_ = v_univApprox_3842_;
v___y_3775_ = v_trackZetaDelta_3835_;
v___y_3776_ = v_localInstances_3838_;
v___y_3777_ = v_zetaDeltaSet_3836_;
v___y_3778_ = v_cacheInferType_3844_;
v___y_3779_ = v_lctx_3837_;
v___y_3780_ = v_canUnfold_x3f_3841_;
v___y_3781_ = v_synthPendingDepth_3840_;
v___y_3782_ = v_inTypeClassResolution_3843_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3871_; 
lean_dec(v_canUnfold_x3f_3841_);
lean_dec(v_synthPendingDepth_3840_);
lean_dec(v_defEqCtx_x3f_3839_);
lean_dec_ref(v_localInstances_3838_);
lean_dec_ref(v_lctx_3837_);
lean_dec(v_zetaDeltaSet_3836_);
v___x_3871_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3764_, v___x_3858_, v_a_3766_, v___y_3811_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v___y_3811_);
lean_dec(v_a_3766_);
lean_dec_ref(v___x_3858_);
return v___x_3871_;
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
v_resetjp_3899_:
{
uint8_t v___y_3903_; lean_object* v___x_3914_; uint8_t v___x_3915_; uint8_t v___x_3916_; 
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_nat_dec_eq(v_maxRecDepth_3887_, v___x_3914_);
v___x_3916_ = lean_bool_not(v___x_3915_);
if (v___x_3916_ == 0)
{
v___y_3903_ = v___x_3916_;
goto v___jp_3902_;
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_nat_dec_eq(v_currRecDepth_3886_, v_maxRecDepth_3887_);
v___y_3903_ = v___x_3917_;
goto v___jp_3902_;
}
v___jp_3902_:
{
if (v___y_3903_ == 0)
{
lean_object* v___x_3904_; uint8_t v_transparency_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3904_ = l_Lean_Meta_Context_config(v_a_3765_);
v_transparency_3905_ = lean_ctor_get_uint8(v___x_3904_, 9);
lean_dec_ref(v___x_3904_);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_add(v_currRecDepth_3886_, v___x_3906_);
lean_dec(v_currRecDepth_3886_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 3, v___x_3907_);
v___x_3909_ = v___x_3900_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_fileName_3883_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_fileMap_3884_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_options_3885_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_maxRecDepth_3887_);
lean_ctor_set(v_reuseFailAlloc_3912_, 5, v_ref_3888_);
lean_ctor_set(v_reuseFailAlloc_3912_, 6, v_currNamespace_3889_);
lean_ctor_set(v_reuseFailAlloc_3912_, 7, v_openDecls_3890_);
lean_ctor_set(v_reuseFailAlloc_3912_, 8, v_initHeartbeats_3891_);
lean_ctor_set(v_reuseFailAlloc_3912_, 9, v_maxHeartbeats_3892_);
lean_ctor_set(v_reuseFailAlloc_3912_, 10, v_quotContext_3893_);
lean_ctor_set(v_reuseFailAlloc_3912_, 11, v_currMacroScope_3894_);
lean_ctor_set(v_reuseFailAlloc_3912_, 12, v_cancelTk_x3f_3896_);
lean_ctor_set(v_reuseFailAlloc_3912_, 13, v_inheritedTraceOptions_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3912_, sizeof(void*)*14, v_diag_3895_);
lean_ctor_set_uint8(v_reuseFailAlloc_3912_, sizeof(void*)*14 + 1, v_suppressElabErrors_3897_);
v___x_3909_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
uint8_t v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = 1;
v___x_3911_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3905_, v___x_3910_);
if (v___x_3911_ == 0)
{
v___y_3811_ = v___x_3909_;
v___y_3812_ = v_transparency_3905_;
goto v___jp_3810_;
}
else
{
v___y_3811_ = v___x_3909_;
v___y_3812_ = v___x_3910_;
goto v___jp_3810_;
}
}
}
else
{
lean_object* v___x_3913_; 
lean_del_object(v___x_3900_);
lean_dec_ref(v_inheritedTraceOptions_3898_);
lean_dec(v_cancelTk_x3f_3896_);
lean_dec(v_currMacroScope_3894_);
lean_dec(v_quotContext_3893_);
lean_dec(v_maxHeartbeats_3892_);
lean_dec(v_initHeartbeats_3891_);
lean_dec(v_openDecls_3890_);
lean_dec(v_currNamespace_3889_);
lean_dec(v_maxRecDepth_3887_);
lean_dec(v_currRecDepth_3886_);
lean_dec_ref(v_options_3885_);
lean_dec_ref(v_fileMap_3884_);
lean_dec_ref(v_fileName_3883_);
lean_dec(v_a_3768_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec_ref(v_e_3764_);
v___x_3913_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3888_);
return v___x_3913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = lean_infer_type(v_e_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
return v_res_3925_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3926_){
_start:
{
switch(lean_obj_tag(v_x_3926_))
{
case 0:
{
uint8_t v___x_3927_; 
v___x_3927_ = 1;
return v___x_3927_;
}
case 2:
{
lean_object* v_a_3928_; lean_object* v_a_3929_; uint8_t v___x_3930_; 
v_a_3928_ = lean_ctor_get(v_x_3926_, 0);
v_a_3929_ = lean_ctor_get(v_x_3926_, 1);
v___x_3930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3928_);
if (v___x_3930_ == 0)
{
return v___x_3930_;
}
else
{
v_x_3926_ = v_a_3929_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3932_; 
v_a_3932_ = lean_ctor_get(v_x_3926_, 1);
v_x_3926_ = v_a_3932_;
goto _start;
}
default: 
{
uint8_t v___x_3934_; 
v___x_3934_ = 0;
return v___x_3934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3935_){
_start:
{
uint8_t v_res_3936_; lean_object* v_r_3937_; 
v_res_3936_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3935_);
lean_dec(v_x_3935_);
v_r_3937_ = lean_box(v_res_3936_);
return v_r_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v_mctx_3942_; lean_object* v___x_3943_; lean_object* v_fst_3944_; lean_object* v_snd_3945_; lean_object* v___x_3946_; lean_object* v_cache_3947_; lean_object* v_zetaDeltaFVarIds_3948_; lean_object* v_postponed_3949_; lean_object* v_diag_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3959_; 
v___x_3941_ = lean_st_ref_get(v___y_3939_);
v_mctx_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc_ref(v_mctx_3942_);
lean_dec(v___x_3941_);
v___x_3943_ = lean_instantiate_level_mvars(v_mctx_3942_, v_l_3938_);
v_fst_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_fst_3944_);
v_snd_3945_ = lean_ctor_get(v___x_3943_, 1);
lean_inc(v_snd_3945_);
lean_dec_ref(v___x_3943_);
v___x_3946_ = lean_st_ref_take(v___y_3939_);
v_cache_3947_ = lean_ctor_get(v___x_3946_, 1);
v_zetaDeltaFVarIds_3948_ = lean_ctor_get(v___x_3946_, 2);
v_postponed_3949_ = lean_ctor_get(v___x_3946_, 3);
v_diag_3950_ = lean_ctor_get(v___x_3946_, 4);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v___x_3946_, 0);
lean_dec(v_unused_3960_);
v___x_3952_ = v___x_3946_;
v_isShared_3953_ = v_isSharedCheck_3959_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_diag_3950_);
lean_inc(v_postponed_3949_);
lean_inc(v_zetaDeltaFVarIds_3948_);
lean_inc(v_cache_3947_);
lean_dec(v___x_3946_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3959_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v_fst_3944_);
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_fst_3944_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_cache_3947_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v_zetaDeltaFVarIds_3948_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v_postponed_3949_);
lean_ctor_set(v_reuseFailAlloc_3958_, 4, v_diag_3950_);
v___x_3955_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_st_ref_set(v___y_3939_, v___x_3955_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_snd_3945_);
return v___x_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3961_, v___y_3962_);
lean_dec(v___y_3962_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3965_, v___y_3967_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3979_, lean_object* v_x_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
switch(lean_obj_tag(v_x_3979_))
{
case 3:
{
lean_object* v_u_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_u_3990_ = lean_ctor_get(v_x_3979_, 0);
lean_inc(v_u_3990_);
lean_dec_ref_known(v_x_3979_, 1);
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = lean_nat_dec_eq(v_x_3980_, v___x_3991_);
lean_dec(v_x_3980_);
if (v___x_3992_ == 0)
{
lean_dec(v_u_3990_);
goto v___jp_3986_;
}
else
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3990_, v_a_3982_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4004_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4004_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4004_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
uint8_t v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_3998_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3994_);
lean_dec(v_a_3994_);
v___x_3999_ = l_Lean_Bool_toLBool(v___x_3998_);
v___x_4000_ = lean_box(v___x_3999_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4000_);
v___x_4002_ = v___x_3996_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3993_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3993_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
case 7:
{
lean_object* v_body_4013_; lean_object* v_zero_4014_; uint8_t v_isZero_4015_; 
v_body_4013_ = lean_ctor_get(v_x_3979_, 2);
lean_inc_ref(v_body_4013_);
lean_dec_ref_known(v_x_3979_, 3);
v_zero_4014_ = lean_unsigned_to_nat(0u);
v_isZero_4015_ = lean_nat_dec_eq(v_x_3980_, v_zero_4014_);
if (v_isZero_4015_ == 1)
{
uint8_t v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_dec_ref(v_body_4013_);
lean_dec(v_x_3980_);
v___x_4016_ = 0;
v___x_4017_ = lean_box(v___x_4016_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v_one_4019_; lean_object* v_n_4020_; 
v_one_4019_ = lean_unsigned_to_nat(1u);
v_n_4020_ = lean_nat_sub(v_x_3980_, v_one_4019_);
lean_dec(v_x_3980_);
v_x_3979_ = v_body_4013_;
v_x_3980_ = v_n_4020_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4022_; 
v_body_4022_ = lean_ctor_get(v_x_3979_, 3);
lean_inc_ref(v_body_4022_);
lean_dec_ref_known(v_x_3979_, 4);
v_x_3979_ = v_body_4022_;
goto _start;
}
case 10:
{
lean_object* v_expr_4024_; 
v_expr_4024_ = lean_ctor_get(v_x_3979_, 1);
lean_inc_ref(v_expr_4024_);
lean_dec_ref_known(v_x_3979_, 2);
v_x_3979_ = v_expr_4024_;
goto _start;
}
default: 
{
lean_dec(v_x_3980_);
lean_dec_ref(v_x_3979_);
goto v___jp_3986_;
}
}
v___jp_3986_:
{
uint8_t v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = 2;
v___x_3988_ = lean_box(v___x_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4026_, v_x_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_4034_, lean_object* v_x_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
switch(lean_obj_tag(v_x_4034_))
{
case 4:
{
lean_object* v_declName_4041_; lean_object* v_us_4042_; lean_object* v___x_4043_; 
v_declName_4041_ = lean_ctor_get(v_x_4034_, 0);
lean_inc(v_declName_4041_);
v_us_4042_ = lean_ctor_get(v_x_4034_, 1);
lean_inc(v_us_4042_);
lean_dec_ref_known(v_x_4034_, 2);
v___x_4043_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4041_, v_us_4042_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4044_, v_x_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v___x_4045_;
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_x_4035_);
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
case 1:
{
lean_object* v_fvarId_4054_; lean_object* v___x_4055_; 
v_fvarId_4054_ = lean_ctor_get(v_x_4034_, 0);
lean_inc(v_fvarId_4054_);
lean_dec_ref_known(v_x_4034_, 1);
v___x_4055_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4054_, v_a_4036_, v_a_4038_, v_a_4039_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4056_, v_x_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v___x_4057_;
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v_x_4035_);
v_a_4058_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4055_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4055_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4066_; lean_object* v___x_4067_; 
v_mvarId_4066_ = lean_ctor_get(v_x_4034_, 0);
lean_inc(v_mvarId_4066_);
lean_dec_ref_known(v_x_4034_, 1);
v___x_4067_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4066_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4068_, v_x_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v___x_4069_;
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_x_4035_);
v_a_4070_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4067_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4067_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
case 5:
{
lean_object* v_fn_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_fn_4078_ = lean_ctor_get(v_x_4034_, 0);
lean_inc_ref(v_fn_4078_);
lean_dec_ref_known(v_x_4034_, 2);
v___x_4079_ = lean_unsigned_to_nat(1u);
v___x_4080_ = lean_nat_add(v_x_4035_, v___x_4079_);
lean_dec(v_x_4035_);
v_x_4034_ = v_fn_4078_;
v_x_4035_ = v___x_4080_;
goto _start;
}
case 10:
{
lean_object* v_expr_4082_; 
v_expr_4082_ = lean_ctor_get(v_x_4034_, 1);
lean_inc_ref(v_expr_4082_);
lean_dec_ref_known(v_x_4034_, 2);
v_x_4034_ = v_expr_4082_;
goto _start;
}
case 8:
{
lean_object* v_body_4084_; 
v_body_4084_ = lean_ctor_get(v_x_4034_, 3);
lean_inc_ref(v_body_4084_);
lean_dec_ref_known(v_x_4034_, 4);
v_x_4034_ = v_body_4084_;
goto _start;
}
case 6:
{
lean_object* v_body_4086_; lean_object* v_zero_4087_; uint8_t v_isZero_4088_; 
v_body_4086_ = lean_ctor_get(v_x_4034_, 2);
lean_inc_ref(v_body_4086_);
lean_dec_ref_known(v_x_4034_, 3);
v_zero_4087_ = lean_unsigned_to_nat(0u);
v_isZero_4088_ = lean_nat_dec_eq(v_x_4035_, v_zero_4087_);
if (v_isZero_4088_ == 1)
{
uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
lean_dec_ref(v_body_4086_);
lean_dec(v_x_4035_);
v___x_4089_ = 0;
v___x_4090_ = lean_box(v___x_4089_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
return v___x_4091_;
}
else
{
lean_object* v_one_4092_; lean_object* v_n_4093_; 
v_one_4092_ = lean_unsigned_to_nat(1u);
v_n_4093_ = lean_nat_sub(v_x_4035_, v_one_4092_);
lean_dec(v_x_4035_);
v_x_4034_ = v_body_4086_;
v_x_4035_ = v_n_4093_;
goto _start;
}
}
default: 
{
uint8_t v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v_x_4035_);
lean_dec_ref(v_x_4034_);
v___x_4095_ = 2;
v___x_4096_ = lean_box(v___x_4095_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4098_, lean_object* v_x_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4098_, v_x_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_){
_start:
{
switch(lean_obj_tag(v_x_4106_))
{
case 0:
{
uint8_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec_ref_known(v_x_4106_, 1);
v___x_4112_ = 2;
v___x_4113_ = lean_box(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
case 1:
{
lean_object* v_fvarId_4115_; lean_object* v___x_4116_; 
v_fvarId_4115_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_fvarId_4115_);
lean_dec_ref_known(v_x_4106_, 1);
v___x_4116_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4115_, v_a_4107_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v___x_4116_, 1);
v___x_4118_ = lean_unsigned_to_nat(0u);
v___x_4119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4117_, v___x_4118_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4119_;
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
v_a_4120_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4116_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4116_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4128_; lean_object* v___x_4129_; 
v_mvarId_4128_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_mvarId_4128_);
lean_dec_ref_known(v_x_4106_, 1);
v___x_4129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4128_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4130_, v___x_4131_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4132_;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4129_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4129_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
case 4:
{
lean_object* v_declName_4141_; lean_object* v_us_4142_; lean_object* v___x_4143_; 
v_declName_4141_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_declName_4141_);
v_us_4142_ = lean_ctor_get(v_x_4106_, 1);
lean_inc(v_us_4142_);
lean_dec_ref_known(v_x_4106_, 2);
v___x_4143_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4141_, v_us_4142_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = lean_unsigned_to_nat(0u);
v___x_4146_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4144_, v___x_4145_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4146_;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_a_4147_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4143_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4143_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
case 5:
{
lean_object* v_fn_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_fn_4155_ = lean_ctor_get(v_x_4106_, 0);
lean_inc_ref(v_fn_4155_);
lean_dec_ref_known(v_x_4106_, 2);
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4155_, v___x_4156_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4157_;
}
case 7:
{
lean_object* v_body_4158_; 
v_body_4158_ = lean_ctor_get(v_x_4106_, 2);
lean_inc_ref(v_body_4158_);
lean_dec_ref_known(v_x_4106_, 3);
v_x_4106_ = v_body_4158_;
goto _start;
}
case 8:
{
lean_object* v_body_4160_; 
v_body_4160_ = lean_ctor_get(v_x_4106_, 3);
lean_inc_ref(v_body_4160_);
lean_dec_ref_known(v_x_4106_, 4);
v_x_4106_ = v_body_4160_;
goto _start;
}
case 10:
{
lean_object* v_expr_4162_; 
v_expr_4162_ = lean_ctor_get(v_x_4106_, 1);
lean_inc_ref(v_expr_4162_);
lean_dec_ref_known(v_x_4106_, 2);
v_x_4106_ = v_expr_4162_;
goto _start;
}
case 11:
{
uint8_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref_known(v_x_4106_, 3);
v___x_4164_ = 2;
v___x_4165_ = lean_box(v___x_4164_);
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
return v___x_4166_;
}
default: 
{
uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec_ref(v_x_4106_);
v___x_4167_ = 0;
v___x_4168_ = lean_box(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Meta_isPropQuick(v_x_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v___x_4183_; 
lean_inc_ref(v_e_4177_);
v___x_4183_ = l_Lean_Meta_isPropQuick(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4240_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4240_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4240_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
uint8_t v___x_4188_; 
v___x_4188_ = lean_unbox(v_a_4184_);
lean_dec(v_a_4184_);
switch(v___x_4188_)
{
case 0:
{
uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4192_; 
lean_dec_ref(v_e_4177_);
v___x_4189_ = 0;
v___x_4190_ = lean_box(v___x_4189_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4190_);
v___x_4192_ = v___x_4186_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
case 1:
{
uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
lean_dec_ref(v_e_4177_);
v___x_4194_ = 1;
v___x_4195_ = lean_box(v___x_4194_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4195_);
v___x_4197_ = v___x_4186_;
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
default: 
{
lean_object* v___x_4199_; 
lean_del_object(v___x_4186_);
lean_inc(v_a_4181_);
lean_inc_ref(v_a_4180_);
lean_inc(v_a_4179_);
lean_inc_ref(v_a_4178_);
v___x_4199_ = lean_infer_type(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = l_Lean_Meta_whnfD(v_a_4200_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4223_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4223_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4223_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
if (lean_obj_tag(v_a_4202_) == 3)
{
lean_object* v_u_4206_; lean_object* v___x_4207_; lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4217_; 
lean_del_object(v___x_4204_);
v_u_4206_ = lean_ctor_get(v_a_4202_, 0);
lean_inc(v_u_4206_);
lean_dec_ref_known(v_a_4202_, 1);
v___x_4207_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4206_, v_a_4179_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4212_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4208_);
lean_dec(v_a_4208_);
v___x_4213_ = lean_box(v___x_4212_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4213_);
v___x_4215_ = v___x_4210_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
else
{
uint8_t v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_dec(v_a_4202_);
v___x_4218_ = 0;
v___x_4219_ = lean_box(v___x_4218_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4219_);
v___x_4221_ = v___x_4204_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4201_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4201_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4199_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4199_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_e_4177_);
v_a_4241_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4183_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4183_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_isProp(v_e_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4256_){
_start:
{
switch(lean_obj_tag(v_x_4256_))
{
case 0:
{
lean_object* v___x_4257_; 
v___x_4257_ = lean_unsigned_to_nat(0u);
return v___x_4257_;
}
case 1:
{
lean_object* v___x_4258_; 
v___x_4258_ = lean_unsigned_to_nat(1u);
return v___x_4258_;
}
case 2:
{
lean_object* v___x_4259_; 
v___x_4259_ = lean_unsigned_to_nat(2u);
return v___x_4259_;
}
default: 
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_unsigned_to_nat(3u);
return v___x_4260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4261_);
lean_dec(v_x_4261_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4263_, lean_object* v_k_4264_){
_start:
{
if (lean_obj_tag(v_t_4263_) == 3)
{
lean_object* v_idx_4265_; lean_object* v___x_4266_; 
v_idx_4265_ = lean_ctor_get(v_t_4263_, 0);
lean_inc(v_idx_4265_);
lean_dec_ref_known(v_t_4263_, 1);
v___x_4266_ = lean_apply_1(v_k_4264_, v_idx_4265_);
return v___x_4266_;
}
else
{
lean_dec(v_t_4263_);
return v_k_4264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4267_, lean_object* v_ctorIdx_4268_, lean_object* v_t_4269_, lean_object* v_h_4270_, lean_object* v_k_4271_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4269_, v_k_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4273_, lean_object* v_ctorIdx_4274_, lean_object* v_t_4275_, lean_object* v_h_4276_, lean_object* v_k_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4273_, v_ctorIdx_4274_, v_t_4275_, v_h_4276_, v_k_4277_);
lean_dec(v_ctorIdx_4274_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4279_, lean_object* v_false_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4279_, v_false_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4282_, lean_object* v_t_4283_, lean_object* v_h_4284_, lean_object* v_false_4285_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4283_, v_false_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4287_, lean_object* v_true_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4287_, v_true_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4290_, lean_object* v_t_4291_, lean_object* v_h_4292_, lean_object* v_true_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4291_, v_true_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4295_, lean_object* v_undef_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4295_, v_undef_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4298_, lean_object* v_t_4299_, lean_object* v_h_4300_, lean_object* v_undef_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4299_, v_undef_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4303_, lean_object* v_bvar_4304_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4303_, v_bvar_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4306_, lean_object* v_t_4307_, lean_object* v_h_4308_, lean_object* v_bvar_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4307_, v_bvar_4309_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4311_){
_start:
{
switch(v_x_4311_)
{
case 0:
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_box(0);
return v___x_4312_;
}
case 1:
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_box(1);
return v___x_4313_;
}
default: 
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_box(2);
return v___x_4314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4315_){
_start:
{
uint8_t v_x_25__boxed_4316_; lean_object* v_res_4317_; 
v_x_25__boxed_4316_ = lean_unbox(v_x_4315_);
v_res_4317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4316_);
return v_res_4317_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4318_){
_start:
{
switch(lean_obj_tag(v_x_4318_))
{
case 0:
{
uint8_t v___x_4319_; 
v___x_4319_ = 0;
return v___x_4319_;
}
case 1:
{
uint8_t v___x_4320_; 
v___x_4320_ = 1;
return v___x_4320_;
}
default: 
{
uint8_t v___x_4321_; 
v___x_4321_ = 2;
return v___x_4321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4322_){
_start:
{
uint8_t v_res_4323_; lean_object* v_r_4324_; 
v_res_4323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4322_);
lean_dec(v_x_4322_);
v_r_4324_ = lean_box(v_res_4323_);
return v_r_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4326_){
_start:
{
switch(lean_obj_tag(v_e_4326_))
{
case 3:
{
lean_object* v_u_4327_; uint8_t v___x_4328_; 
v_u_4327_ = lean_ctor_get(v_e_4326_, 0);
v___x_4328_ = l_Lean_Level_isNeverZero(v_u_4327_);
if (v___x_4328_ == 0)
{
uint8_t v___x_4329_; 
v___x_4329_ = l_Lean_Level_isZero(v_u_4327_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_box(2);
return v___x_4330_;
}
else
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_box(1);
return v___x_4331_;
}
}
else
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_box(0);
return v___x_4332_;
}
}
case 5:
{
lean_object* v_fn_4333_; 
v_fn_4333_ = lean_ctor_get(v_e_4326_, 0);
if (lean_obj_tag(v_fn_4333_) == 4)
{
lean_object* v_declName_4334_; 
v_declName_4334_ = lean_ctor_get(v_fn_4333_, 0);
if (lean_obj_tag(v_declName_4334_) == 1)
{
lean_object* v_pre_4335_; 
v_pre_4335_ = lean_ctor_get(v_declName_4334_, 0);
if (lean_obj_tag(v_pre_4335_) == 0)
{
lean_object* v_arg_4336_; lean_object* v_str_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_arg_4336_ = lean_ctor_get(v_e_4326_, 1);
v_str_4337_ = lean_ctor_get(v_declName_4334_, 1);
v___x_4338_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4339_ = lean_string_dec_eq(v_str_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_box(2);
return v___x_4340_;
}
else
{
v_e_4326_ = v_arg_4336_;
goto _start;
}
}
else
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_box(2);
return v___x_4342_;
}
}
else
{
lean_object* v___x_4343_; 
v___x_4343_ = lean_box(2);
return v___x_4343_;
}
}
else
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_box(2);
return v___x_4344_;
}
}
default: 
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_box(2);
return v___x_4345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4346_);
lean_dec_ref(v_e_4346_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4348_, lean_object* v_binderType_4349_){
_start:
{
if (lean_obj_tag(v_r_4348_) == 3)
{
lean_object* v_idx_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4362_; 
v_idx_4350_ = lean_ctor_get(v_r_4348_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_r_4348_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4352_ = v_r_4348_;
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_idx_4350_);
lean_dec(v_r_4348_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v_zero_4354_; uint8_t v_isZero_4355_; 
v_zero_4354_ = lean_unsigned_to_nat(0u);
v_isZero_4355_ = lean_nat_dec_eq(v_idx_4350_, v_zero_4354_);
if (v_isZero_4355_ == 1)
{
lean_object* v___x_4356_; 
lean_del_object(v___x_4352_);
lean_dec(v_idx_4350_);
v___x_4356_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4349_);
return v___x_4356_;
}
else
{
lean_object* v_one_4357_; lean_object* v_n_4358_; lean_object* v___x_4360_; 
v_one_4357_ = lean_unsigned_to_nat(1u);
v_n_4358_ = lean_nat_sub(v_idx_4350_, v_one_4357_);
lean_dec(v_idx_4350_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v_n_4358_);
v___x_4360_ = v___x_4352_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_n_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
return v_r_4348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4363_, lean_object* v_binderType_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4363_, v_binderType_4364_);
lean_dec_ref(v_binderType_4364_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4366_, lean_object* v_x_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_type_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; 
switch(lean_obj_tag(v_x_4366_))
{
case 7:
{
lean_object* v_binderType_4401_; lean_object* v_body_4402_; lean_object* v_zero_4403_; uint8_t v_isZero_4404_; 
v_binderType_4401_ = lean_ctor_get(v_x_4366_, 1);
v_body_4402_ = lean_ctor_get(v_x_4366_, 2);
v_zero_4403_ = lean_unsigned_to_nat(0u);
v_isZero_4404_ = lean_nat_dec_eq(v_x_4367_, v_zero_4403_);
if (v_isZero_4404_ == 1)
{
v_type_4374_ = v_x_4366_;
v___y_4375_ = v_a_4368_;
v___y_4376_ = v_a_4369_;
v___y_4377_ = v_a_4370_;
v___y_4378_ = v_a_4371_;
goto v___jp_4373_;
}
else
{
lean_object* v_one_4405_; lean_object* v_n_4406_; lean_object* v___x_4407_; 
lean_inc_ref(v_body_4402_);
lean_inc_ref(v_binderType_4401_);
lean_dec_ref_known(v_x_4366_, 3);
v_one_4405_ = lean_unsigned_to_nat(1u);
v_n_4406_ = lean_nat_sub(v_x_4367_, v_one_4405_);
v___x_4407_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4402_, v_n_4406_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
lean_dec(v_n_4406_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4416_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4416_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4416_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4408_, v_binderType_4401_);
lean_dec_ref(v_binderType_4401_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4412_);
v___x_4414_ = v___x_4410_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
else
{
lean_dec_ref(v_binderType_4401_);
return v___x_4407_;
}
}
}
case 8:
{
lean_object* v_type_4417_; lean_object* v_body_4418_; lean_object* v___x_4419_; 
v_type_4417_ = lean_ctor_get(v_x_4366_, 1);
lean_inc_ref(v_type_4417_);
v_body_4418_ = lean_ctor_get(v_x_4366_, 3);
lean_inc_ref(v_body_4418_);
lean_dec_ref_known(v_x_4366_, 4);
v___x_4419_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4418_, v_x_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4428_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4428_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4420_, v_type_4417_);
lean_dec_ref(v_type_4417_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4424_);
v___x_4426_ = v___x_4422_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
else
{
lean_dec_ref(v_type_4417_);
return v___x_4419_;
}
}
case 10:
{
lean_object* v_expr_4429_; 
v_expr_4429_ = lean_ctor_get(v_x_4366_, 1);
lean_inc_ref(v_expr_4429_);
lean_dec_ref_known(v_x_4366_, 2);
v_x_4366_ = v_expr_4429_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v_deBruijnIndex_4431_ = lean_ctor_get(v_x_4366_, 0);
lean_inc(v_deBruijnIndex_4431_);
lean_dec_ref_known(v_x_4366_, 1);
v___x_4432_ = lean_unsigned_to_nat(0u);
v___x_4433_ = lean_nat_dec_eq(v_x_4367_, v___x_4432_);
if (v___x_4433_ == 0)
{
lean_dec(v_deBruijnIndex_4431_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4434_, 0, v_deBruijnIndex_4431_);
v___x_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
return v___x_4435_;
}
}
default: 
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = lean_nat_dec_eq(v_x_4367_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_dec_ref(v_x_4366_);
goto v___jp_4398_;
}
else
{
v_type_4374_ = v_x_4366_;
v___y_4375_ = v_a_4368_;
v___y_4376_ = v_a_4369_;
v___y_4377_ = v_a_4370_;
v___y_4378_ = v_a_4371_;
goto v___jp_4373_;
}
}
}
v___jp_4373_:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_Meta_isPropQuick(v_type_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4389_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4389_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4384_ = lean_unbox(v_a_4380_);
lean_dec(v_a_4380_);
v___x_4385_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4384_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4385_);
v___x_4387_ = v___x_4382_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_a_4390_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4379_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4379_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
v___jp_4398_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = lean_box(2);
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4438_, lean_object* v_x_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4438_, v_x_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
lean_dec(v_x_4439_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4446_, lean_object* v_n_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4446_, v_n_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4463_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4456_ = v___x_4453_;
v_isShared_4457_ = v_isSharedCheck_4463_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4453_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4463_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
uint8_t v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; 
v___x_4458_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4454_);
lean_dec(v_a_4454_);
v___x_4459_ = lean_box(v___x_4458_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v___x_4459_);
v___x_4461_ = v___x_4456_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
v_a_4464_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4453_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4453_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4472_, lean_object* v_n_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4472_, v_n_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec(v_n_4473_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4480_, lean_object* v_x_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
switch(lean_obj_tag(v_x_4480_))
{
case 4:
{
lean_object* v_declName_4487_; lean_object* v_us_4488_; lean_object* v___x_4489_; 
v_declName_4487_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_declName_4487_);
v_us_4488_ = lean_ctor_get(v_x_4480_, 1);
lean_inc(v_us_4488_);
lean_dec_ref_known(v_x_4480_, 2);
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4487_, v_us_4488_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4490_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_x_4481_);
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
case 1:
{
lean_object* v_fvarId_4500_; lean_object* v___x_4501_; 
v_fvarId_4500_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_fvarId_4500_);
lean_dec_ref_known(v_x_4480_, 1);
v___x_4501_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4500_, v_a_4482_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4502_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4503_;
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_x_4481_);
v_a_4504_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4501_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4501_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4512_; lean_object* v___x_4513_; 
v_mvarId_4512_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_mvarId_4512_);
lean_dec_ref_known(v_x_4480_, 1);
v___x_4513_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4512_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4514_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4515_;
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_x_4481_);
v_a_4516_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4513_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4513_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
case 5:
{
lean_object* v_fn_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_fn_4524_ = lean_ctor_get(v_x_4480_, 0);
lean_inc_ref(v_fn_4524_);
lean_dec_ref_known(v_x_4480_, 2);
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = lean_nat_add(v_x_4481_, v___x_4525_);
lean_dec(v_x_4481_);
v_x_4480_ = v_fn_4524_;
v_x_4481_ = v___x_4526_;
goto _start;
}
case 10:
{
lean_object* v_expr_4528_; 
v_expr_4528_ = lean_ctor_get(v_x_4480_, 1);
lean_inc_ref(v_expr_4528_);
lean_dec_ref_known(v_x_4480_, 2);
v_x_4480_ = v_expr_4528_;
goto _start;
}
case 8:
{
lean_object* v_body_4530_; 
v_body_4530_ = lean_ctor_get(v_x_4480_, 3);
lean_inc_ref(v_body_4530_);
lean_dec_ref_known(v_x_4480_, 4);
v_x_4480_ = v_body_4530_;
goto _start;
}
case 6:
{
lean_object* v_body_4532_; lean_object* v_zero_4533_; uint8_t v_isZero_4534_; 
v_body_4532_ = lean_ctor_get(v_x_4480_, 2);
lean_inc_ref(v_body_4532_);
lean_dec_ref_known(v_x_4480_, 3);
v_zero_4533_ = lean_unsigned_to_nat(0u);
v_isZero_4534_ = lean_nat_dec_eq(v_x_4481_, v_zero_4533_);
if (v_isZero_4534_ == 1)
{
lean_object* v___x_4535_; 
lean_dec(v_x_4481_);
v___x_4535_ = l_Lean_Meta_isProofQuick(v_body_4532_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
return v___x_4535_;
}
else
{
lean_object* v_one_4536_; lean_object* v_n_4537_; 
v_one_4536_ = lean_unsigned_to_nat(1u);
v_n_4537_ = lean_nat_sub(v_x_4481_, v_one_4536_);
lean_dec(v_x_4481_);
v_x_4480_ = v_body_4532_;
v_x_4481_ = v_n_4537_;
goto _start;
}
}
default: 
{
uint8_t v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
lean_dec(v_x_4481_);
lean_dec_ref(v_x_4480_);
v___x_4539_ = 2;
v___x_4540_ = lean_box(v___x_4539_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
switch(lean_obj_tag(v_x_4542_))
{
case 0:
{
uint8_t v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
lean_dec_ref_known(v_x_4542_, 1);
v___x_4548_ = 2;
v___x_4549_ = lean_box(v___x_4548_);
v___x_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
return v___x_4550_;
}
case 1:
{
lean_object* v_fvarId_4551_; lean_object* v___x_4552_; 
v_fvarId_4551_ = lean_ctor_get(v_x_4542_, 0);
lean_inc(v_fvarId_4551_);
lean_dec_ref_known(v_x_4542_, 1);
v___x_4552_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4551_, v_a_4543_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4552_, 1);
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4553_, v___x_4554_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4555_;
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_a_4556_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4552_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4552_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4564_; lean_object* v___x_4565_; 
v_mvarId_4564_ = lean_ctor_get(v_x_4542_, 0);
lean_inc(v_mvarId_4564_);
lean_dec_ref_known(v_x_4542_, 1);
v___x_4565_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4564_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = lean_unsigned_to_nat(0u);
v___x_4568_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4566_, v___x_4567_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4568_;
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
v_a_4569_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4565_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4565_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
case 4:
{
lean_object* v_declName_4577_; lean_object* v_us_4578_; lean_object* v___x_4579_; 
v_declName_4577_ = lean_ctor_get(v_x_4542_, 0);
lean_inc(v_declName_4577_);
v_us_4578_ = lean_ctor_get(v_x_4542_, 1);
lean_inc(v_us_4578_);
lean_dec_ref_known(v_x_4542_, 2);
v___x_4579_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4577_, v_us_4578_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4581_ = lean_unsigned_to_nat(0u);
v___x_4582_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4580_, v___x_4581_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4582_;
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
v_a_4583_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4579_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4579_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
case 5:
{
lean_object* v_fn_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_fn_4591_ = lean_ctor_get(v_x_4542_, 0);
lean_inc_ref(v_fn_4591_);
lean_dec_ref_known(v_x_4542_, 2);
v___x_4592_ = lean_unsigned_to_nat(1u);
v___x_4593_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4591_, v___x_4592_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4593_;
}
case 6:
{
lean_object* v_body_4594_; 
v_body_4594_ = lean_ctor_get(v_x_4542_, 2);
lean_inc_ref(v_body_4594_);
lean_dec_ref_known(v_x_4542_, 3);
v_x_4542_ = v_body_4594_;
goto _start;
}
case 8:
{
lean_object* v_body_4596_; 
v_body_4596_ = lean_ctor_get(v_x_4542_, 3);
lean_inc_ref(v_body_4596_);
lean_dec_ref_known(v_x_4542_, 4);
v_x_4542_ = v_body_4596_;
goto _start;
}
case 10:
{
lean_object* v_expr_4598_; 
v_expr_4598_ = lean_ctor_get(v_x_4542_, 1);
lean_inc_ref(v_expr_4598_);
lean_dec_ref_known(v_x_4542_, 2);
v_x_4542_ = v_expr_4598_;
goto _start;
}
case 11:
{
uint8_t v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
lean_dec_ref_known(v_x_4542_, 3);
v___x_4600_ = 2;
v___x_4601_ = lean_box(v___x_4600_);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
return v___x_4602_;
}
default: 
{
uint8_t v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
lean_dec_ref(v_x_4542_);
v___x_4603_ = 0;
v___x_4604_ = lean_box(v___x_4603_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_Meta_isProofQuick(v_x_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4613_, lean_object* v_x_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4613_, v_x_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v___x_4627_; 
lean_inc_ref(v_e_4621_);
v___x_4627_ = l_Lean_Meta_isProofQuick(v_e_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4654_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4630_ = v___x_4627_;
v_isShared_4631_ = v_isSharedCheck_4654_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4627_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4654_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
uint8_t v___x_4632_; 
v___x_4632_ = lean_unbox(v_a_4628_);
lean_dec(v_a_4628_);
switch(v___x_4632_)
{
case 0:
{
uint8_t v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
lean_dec_ref(v_e_4621_);
v___x_4633_ = 0;
v___x_4634_ = lean_box(v___x_4633_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4634_);
v___x_4636_ = v___x_4630_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
case 1:
{
uint8_t v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
lean_dec_ref(v_e_4621_);
v___x_4638_ = 1;
v___x_4639_ = lean_box(v___x_4638_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4639_);
v___x_4641_ = v___x_4630_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
default: 
{
lean_object* v___x_4643_; 
lean_del_object(v___x_4630_);
lean_inc(v_a_4625_);
lean_inc_ref(v_a_4624_);
lean_inc(v_a_4623_);
lean_inc_ref(v_a_4622_);
v___x_4643_ = lean_infer_type(v_e_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4645_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
v___x_4645_ = l_Lean_Meta_isProp(v_a_4644_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
return v___x_4645_;
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
v_a_4646_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4643_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4643_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec_ref(v_e_4621_);
v_a_4655_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4627_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4627_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_Meta_isProof(v_e_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4670_, lean_object* v_x_4671_){
_start:
{
switch(lean_obj_tag(v_x_4670_))
{
case 3:
{
lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4677_ = lean_unsigned_to_nat(0u);
v___x_4678_ = lean_nat_dec_eq(v_x_4671_, v___x_4677_);
lean_dec(v_x_4671_);
if (v___x_4678_ == 0)
{
goto v___jp_4673_;
}
else
{
uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = 1;
v___x_4680_ = lean_box(v___x_4679_);
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
return v___x_4681_;
}
}
case 7:
{
lean_object* v_body_4682_; lean_object* v_zero_4683_; uint8_t v_isZero_4684_; 
v_body_4682_ = lean_ctor_get(v_x_4670_, 2);
v_zero_4683_ = lean_unsigned_to_nat(0u);
v_isZero_4684_ = lean_nat_dec_eq(v_x_4671_, v_zero_4683_);
if (v_isZero_4684_ == 1)
{
uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
lean_dec(v_x_4671_);
v___x_4685_ = 0;
v___x_4686_ = lean_box(v___x_4685_);
v___x_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
return v___x_4687_;
}
else
{
lean_object* v_one_4688_; lean_object* v_n_4689_; 
v_one_4688_ = lean_unsigned_to_nat(1u);
v_n_4689_ = lean_nat_sub(v_x_4671_, v_one_4688_);
lean_dec(v_x_4671_);
v_x_4670_ = v_body_4682_;
v_x_4671_ = v_n_4689_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4691_; 
v_body_4691_ = lean_ctor_get(v_x_4670_, 3);
v_x_4670_ = v_body_4691_;
goto _start;
}
case 10:
{
lean_object* v_expr_4693_; 
v_expr_4693_ = lean_ctor_get(v_x_4670_, 1);
v_x_4670_ = v_expr_4693_;
goto _start;
}
default: 
{
lean_dec(v_x_4671_);
goto v___jp_4673_;
}
}
v___jp_4673_:
{
uint8_t v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = 2;
v___x_4675_ = lean_box(v___x_4674_);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
return v___x_4676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4695_, lean_object* v_x_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4695_, v_x_4696_);
lean_dec_ref(v_x_4695_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4699_, lean_object* v_x_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4699_, v_x_4700_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4707_, lean_object* v_x_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4707_, v_x_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec_ref(v_x_4707_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4715_, lean_object* v_x_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
switch(lean_obj_tag(v_x_4715_))
{
case 4:
{
lean_object* v_declName_4722_; lean_object* v_us_4723_; lean_object* v___x_4724_; 
v_declName_4722_ = lean_ctor_get(v_x_4715_, 0);
lean_inc(v_declName_4722_);
v_us_4723_ = lean_ctor_get(v_x_4715_, 1);
lean_inc(v_us_4723_);
lean_dec_ref_known(v_x_4715_, 2);
v___x_4724_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4722_, v_us_4723_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4726_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___x_4724_, 1);
v___x_4726_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4725_, v_x_4716_);
lean_dec(v_a_4725_);
return v___x_4726_;
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec(v_x_4716_);
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
case 1:
{
lean_object* v_fvarId_4735_; lean_object* v___x_4736_; 
v_fvarId_4735_ = lean_ctor_get(v_x_4715_, 0);
lean_inc(v_fvarId_4735_);
lean_dec_ref_known(v_x_4715_, 1);
v___x_4736_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4735_, v_a_4717_, v_a_4719_, v_a_4720_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4738_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4737_, v_x_4716_);
lean_dec(v_a_4737_);
return v___x_4738_;
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
lean_dec(v_x_4716_);
v_a_4739_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4741_ = v___x_4736_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4736_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4747_; lean_object* v___x_4748_; 
v_mvarId_4747_ = lean_ctor_get(v_x_4715_, 0);
lean_inc(v_mvarId_4747_);
lean_dec_ref_known(v_x_4715_, 1);
v___x_4748_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4747_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4750_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref_known(v___x_4748_, 1);
v___x_4750_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4749_, v_x_4716_);
lean_dec(v_a_4749_);
return v___x_4750_;
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec(v_x_4716_);
v_a_4751_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4748_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4748_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
case 5:
{
lean_object* v_fn_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v_fn_4759_ = lean_ctor_get(v_x_4715_, 0);
lean_inc_ref(v_fn_4759_);
lean_dec_ref_known(v_x_4715_, 2);
v___x_4760_ = lean_unsigned_to_nat(1u);
v___x_4761_ = lean_nat_add(v_x_4716_, v___x_4760_);
lean_dec(v_x_4716_);
v_x_4715_ = v_fn_4759_;
v_x_4716_ = v___x_4761_;
goto _start;
}
case 10:
{
lean_object* v_expr_4763_; 
v_expr_4763_ = lean_ctor_get(v_x_4715_, 1);
lean_inc_ref(v_expr_4763_);
lean_dec_ref_known(v_x_4715_, 2);
v_x_4715_ = v_expr_4763_;
goto _start;
}
case 8:
{
lean_object* v_body_4765_; 
v_body_4765_ = lean_ctor_get(v_x_4715_, 3);
lean_inc_ref(v_body_4765_);
lean_dec_ref_known(v_x_4715_, 4);
v_x_4715_ = v_body_4765_;
goto _start;
}
case 6:
{
lean_object* v_body_4767_; lean_object* v_zero_4768_; uint8_t v_isZero_4769_; 
v_body_4767_ = lean_ctor_get(v_x_4715_, 2);
lean_inc_ref(v_body_4767_);
lean_dec_ref_known(v_x_4715_, 3);
v_zero_4768_ = lean_unsigned_to_nat(0u);
v_isZero_4769_ = lean_nat_dec_eq(v_x_4716_, v_zero_4768_);
if (v_isZero_4769_ == 1)
{
uint8_t v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec_ref(v_body_4767_);
lean_dec(v_x_4716_);
v___x_4770_ = 0;
v___x_4771_ = lean_box(v___x_4770_);
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
else
{
lean_object* v_one_4773_; lean_object* v_n_4774_; 
v_one_4773_ = lean_unsigned_to_nat(1u);
v_n_4774_ = lean_nat_sub(v_x_4716_, v_one_4773_);
lean_dec(v_x_4716_);
v_x_4715_ = v_body_4767_;
v_x_4716_ = v_n_4774_;
goto _start;
}
}
default: 
{
uint8_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
lean_dec(v_x_4716_);
lean_dec_ref(v_x_4715_);
v___x_4776_ = 2;
v___x_4777_ = lean_box(v___x_4776_);
v___x_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
return v___x_4778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4779_, lean_object* v_x_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4779_, v_x_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
switch(lean_obj_tag(v_x_4787_))
{
case 1:
{
lean_object* v_fvarId_4793_; lean_object* v___x_4794_; 
v_fvarId_4793_ = lean_ctor_get(v_x_4787_, 0);
lean_inc(v_fvarId_4793_);
lean_dec_ref_known(v_x_4787_, 1);
v___x_4794_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4793_, v_a_4788_, v_a_4790_, v_a_4791_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4795_);
lean_dec_ref_known(v___x_4794_, 1);
v___x_4796_ = lean_unsigned_to_nat(0u);
v___x_4797_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4795_, v___x_4796_);
lean_dec(v_a_4795_);
return v___x_4797_;
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
v_a_4798_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4794_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4794_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4806_; lean_object* v___x_4807_; 
v_mvarId_4806_ = lean_ctor_get(v_x_4787_, 0);
lean_inc(v_mvarId_4806_);
lean_dec_ref_known(v_x_4787_, 1);
v___x_4807_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4806_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v___x_4807_, 1);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4808_, v___x_4809_);
lean_dec(v_a_4808_);
return v___x_4810_;
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
v_a_4811_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4807_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4807_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
case 3:
{
uint8_t v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_dec_ref_known(v_x_4787_, 1);
v___x_4819_ = 1;
v___x_4820_ = lean_box(v___x_4819_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
case 4:
{
lean_object* v_declName_4822_; lean_object* v_us_4823_; lean_object* v___x_4824_; 
v_declName_4822_ = lean_ctor_get(v_x_4787_, 0);
lean_inc(v_declName_4822_);
v_us_4823_ = lean_ctor_get(v_x_4787_, 1);
lean_inc(v_us_4823_);
lean_dec_ref_known(v_x_4787_, 2);
v___x_4824_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4822_, v_us_4823_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v___x_4826_ = lean_unsigned_to_nat(0u);
v___x_4827_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4825_, v___x_4826_);
lean_dec(v_a_4825_);
return v___x_4827_;
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
v_a_4828_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4824_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4824_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
case 5:
{
lean_object* v_fn_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_fn_4836_ = lean_ctor_get(v_x_4787_, 0);
lean_inc_ref(v_fn_4836_);
lean_dec_ref_known(v_x_4787_, 2);
v___x_4837_ = lean_unsigned_to_nat(1u);
v___x_4838_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4836_, v___x_4837_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
return v___x_4838_;
}
case 6:
{
uint8_t v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
lean_dec_ref_known(v_x_4787_, 3);
v___x_4839_ = 0;
v___x_4840_ = lean_box(v___x_4839_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
case 7:
{
uint8_t v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
lean_dec_ref_known(v_x_4787_, 3);
v___x_4842_ = 1;
v___x_4843_ = lean_box(v___x_4842_);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
case 8:
{
lean_object* v_body_4845_; 
v_body_4845_ = lean_ctor_get(v_x_4787_, 3);
lean_inc_ref(v_body_4845_);
lean_dec_ref_known(v_x_4787_, 4);
v_x_4787_ = v_body_4845_;
goto _start;
}
case 9:
{
uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_dec_ref_known(v_x_4787_, 1);
v___x_4847_ = 0;
v___x_4848_ = lean_box(v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
case 10:
{
lean_object* v_expr_4850_; 
v_expr_4850_ = lean_ctor_get(v_x_4787_, 1);
lean_inc_ref(v_expr_4850_);
lean_dec_ref_known(v_x_4787_, 2);
v_x_4787_ = v_expr_4850_;
goto _start;
}
default: 
{
uint8_t v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
lean_dec_ref(v_x_4787_);
v___x_4852_ = 2;
v___x_4853_ = lean_box(v___x_4852_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
return v___x_4854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Meta_isTypeQuick(v_x_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___x_4868_; 
lean_inc_ref(v_e_4862_);
v___x_4868_ = l_Lean_Meta_isTypeQuick(v_e_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4918_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4871_ = v___x_4868_;
v_isShared_4872_ = v_isSharedCheck_4918_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4868_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4918_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
uint8_t v___x_4873_; 
v___x_4873_ = lean_unbox(v_a_4869_);
lean_dec(v_a_4869_);
switch(v___x_4873_)
{
case 0:
{
uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4877_; 
lean_dec_ref(v_e_4862_);
v___x_4874_ = 0;
v___x_4875_ = lean_box(v___x_4874_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4875_);
v___x_4877_ = v___x_4871_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
case 1:
{
uint8_t v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
lean_dec_ref(v_e_4862_);
v___x_4879_ = 1;
v___x_4880_ = lean_box(v___x_4879_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4880_);
v___x_4882_ = v___x_4871_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
default: 
{
lean_object* v___x_4884_; 
lean_del_object(v___x_4871_);
lean_inc(v_a_4866_);
lean_inc_ref(v_a_4865_);
lean_inc(v_a_4864_);
lean_inc_ref(v_a_4863_);
v___x_4884_ = lean_infer_type(v_e_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4886_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v___x_4886_ = l_Lean_Meta_whnfD(v_a_4885_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4901_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4901_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4901_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
if (lean_obj_tag(v_a_4887_) == 3)
{
uint8_t v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_dec_ref_known(v_a_4887_, 1);
v___x_4891_ = 1;
v___x_4892_ = lean_box(v___x_4891_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4892_);
v___x_4894_ = v___x_4889_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
else
{
uint8_t v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4899_; 
lean_dec(v_a_4887_);
v___x_4896_ = 0;
v___x_4897_ = lean_box(v___x_4896_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4897_);
v___x_4899_ = v___x_4889_;
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
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
v_a_4902_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4886_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4886_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
v_a_4910_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4884_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4884_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec_ref(v_e_4862_);
v_a_4919_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4868_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4868_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Meta_isType(v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4934_){
_start:
{
switch(lean_obj_tag(v_x_4934_))
{
case 7:
{
lean_object* v_body_4935_; 
v_body_4935_ = lean_ctor_get(v_x_4934_, 2);
v_x_4934_ = v_body_4935_;
goto _start;
}
case 3:
{
lean_object* v_u_4937_; lean_object* v___x_4938_; 
v_u_4937_ = lean_ctor_get(v_x_4934_, 0);
lean_inc(v_u_4937_);
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_u_4937_);
return v___x_4938_;
}
default: 
{
lean_object* v___x_4939_; 
v___x_4939_ = lean_box(0);
return v___x_4939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4940_);
lean_dec_ref(v_x_4940_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4942_, lean_object* v_body_4943_, lean_object* v_x_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4942_, v_body_4943_, v_x_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4953_, lean_object* v_xs_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
switch(lean_obj_tag(v_type_4953_))
{
case 3:
{
lean_object* v_u_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
lean_dec_ref(v_xs_4954_);
v_u_4960_ = lean_ctor_get(v_type_4953_, 0);
lean_inc(v_u_4960_);
lean_dec_ref_known(v_type_4953_, 1);
v___x_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4961_, 0, v_u_4960_);
v___x_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4961_);
return v___x_4962_;
}
case 7:
{
lean_object* v_binderName_4963_; lean_object* v_binderType_4964_; lean_object* v_body_4965_; uint8_t v_binderInfo_4966_; lean_object* v___f_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v_binderName_4963_ = lean_ctor_get(v_type_4953_, 0);
lean_inc(v_binderName_4963_);
v_binderType_4964_ = lean_ctor_get(v_type_4953_, 1);
lean_inc_ref(v_binderType_4964_);
v_body_4965_ = lean_ctor_get(v_type_4953_, 2);
lean_inc_ref(v_body_4965_);
v_binderInfo_4966_ = lean_ctor_get_uint8(v_type_4953_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4953_, 3);
lean_inc_ref(v_xs_4954_);
v___f_4967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4967_, 0, v_xs_4954_);
lean_closure_set(v___f_4967_, 1, v_body_4965_);
v___x_4968_ = lean_expr_instantiate_rev(v_binderType_4964_, v_xs_4954_);
lean_dec_ref(v_xs_4954_);
lean_dec_ref(v_binderType_4964_);
v___x_4969_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4963_, v_binderInfo_4966_, v___x_4968_, v___f_4967_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
return v___x_4969_;
}
default: 
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = lean_expr_instantiate_rev(v_type_4953_, v_xs_4954_);
lean_dec_ref(v_xs_4954_);
lean_dec_ref(v_type_4953_);
v___x_4971_ = l_Lean_Meta_whnfD(v___x_4970_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4987_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4974_ = v___x_4971_;
v_isShared_4975_ = v_isSharedCheck_4987_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4971_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4987_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
switch(lean_obj_tag(v_a_4972_))
{
case 3:
{
lean_object* v_u_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
v_u_4976_ = lean_ctor_get(v_a_4972_, 0);
lean_inc(v_u_4976_);
lean_dec_ref_known(v_a_4972_, 1);
v___x_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4977_, 0, v_u_4976_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v___x_4977_);
v___x_4979_ = v___x_4974_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
case 7:
{
lean_object* v___x_4981_; 
lean_del_object(v___x_4974_);
v___x_4981_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4953_ = v_a_4972_;
v_xs_4954_ = v___x_4981_;
goto _start;
}
default: 
{
lean_object* v___x_4983_; lean_object* v___x_4985_; 
lean_dec(v_a_4972_);
v___x_4983_ = lean_box(0);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v___x_4983_);
v___x_4985_ = v___x_4974_;
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
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
v_a_4988_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4971_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4971_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4996_, lean_object* v_body_4997_, lean_object* v_x_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = lean_array_push(v_xs_4996_, v_x_4998_);
v___x_5005_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4997_, v___x_5004_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5006_, lean_object* v_xs_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5006_, v_xs_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5014_, lean_object* v_cache_5015_, lean_object* v_a_x3f_5016_){
_start:
{
lean_object* v___x_5018_; lean_object* v_mctx_5019_; lean_object* v_zetaDeltaFVarIds_5020_; lean_object* v_postponed_5021_; lean_object* v_diag_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5032_; 
v___x_5018_ = lean_st_ref_take(v_a_5014_);
v_mctx_5019_ = lean_ctor_get(v___x_5018_, 0);
v_zetaDeltaFVarIds_5020_ = lean_ctor_get(v___x_5018_, 2);
v_postponed_5021_ = lean_ctor_get(v___x_5018_, 3);
v_diag_5022_ = lean_ctor_get(v___x_5018_, 4);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v___x_5018_, 1);
lean_dec(v_unused_5033_);
v___x_5024_ = v___x_5018_;
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_diag_5022_);
lean_inc(v_postponed_5021_);
lean_inc(v_zetaDeltaFVarIds_5020_);
lean_inc(v_mctx_5019_);
lean_dec(v___x_5018_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v_cache_5015_);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_mctx_5019_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_cache_5015_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_zetaDeltaFVarIds_5020_);
lean_ctor_set(v_reuseFailAlloc_5031_, 3, v_postponed_5021_);
lean_ctor_set(v_reuseFailAlloc_5031_, 4, v_diag_5022_);
v___x_5027_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = lean_st_ref_set(v_a_5014_, v___x_5027_);
v___x_5029_ = lean_box(0);
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
return v___x_5030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5034_, lean_object* v_cache_5035_, lean_object* v_a_x3f_5036_, lean_object* v___y_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5034_, v_cache_5035_, v_a_x3f_5036_);
lean_dec(v_a_x3f_5036_);
lean_dec(v_a_5034_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v___x_5045_; 
v___x_5045_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5039_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v___x_5046_; lean_object* v_cache_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5046_ = lean_st_ref_get(v_a_5041_);
v_cache_5047_ = lean_ctor_get(v___x_5046_, 1);
lean_inc_ref(v_cache_5047_);
lean_dec(v___x_5046_);
v___x_5048_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5049_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5039_, v___x_5048_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5066_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5066_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5066_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
lean_inc(v_a_5050_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set_tag(v___x_5052_, 1);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
v___x_5056_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5041_, v_cache_5047_, v___x_5055_);
lean_dec_ref(v___x_5055_);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5063_ == 0)
{
lean_object* v_unused_5064_; 
v_unused_5064_ = lean_ctor_get(v___x_5056_, 0);
lean_dec(v_unused_5064_);
v___x_5058_ = v___x_5056_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_dec(v___x_5056_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v_a_5050_);
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5050_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
v_a_5067_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5068_ = lean_box(0);
v___x_5069_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5041_, v_cache_5047_, v___x_5068_);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5076_ == 0)
{
lean_object* v_unused_5077_; 
v_unused_5077_ = lean_ctor_get(v___x_5069_, 0);
lean_dec(v_unused_5077_);
v___x_5071_ = v___x_5069_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_dec(v___x_5069_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set_tag(v___x_5071_, 1);
lean_ctor_set(v___x_5071_, 0, v_a_5067_);
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5067_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v___x_5078_; 
lean_dec_ref(v_type_5039_);
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5045_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5107_; 
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5095_ = v___x_5092_;
v_isShared_5096_ = v_isSharedCheck_5107_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5107_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
if (lean_obj_tag(v_a_5093_) == 0)
{
uint8_t v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5097_ = 0;
v___x_5098_ = lean_box(v___x_5097_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5098_);
v___x_5100_ = v___x_5095_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
else
{
uint8_t v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5105_; 
lean_dec_ref_known(v_a_5093_, 1);
v___x_5102_ = 1;
v___x_5103_ = lean_box(v___x_5102_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5103_);
v___x_5105_ = v___x_5095_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5103_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
v_a_5108_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5092_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5092_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Meta_isTypeFormerType(v_type_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
return v_res_5122_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5123_, lean_object* v_x_5124_){
_start:
{
if (lean_obj_tag(v_x_5123_) == 0)
{
if (lean_obj_tag(v_x_5124_) == 0)
{
uint8_t v___x_5125_; 
v___x_5125_ = 1;
return v___x_5125_;
}
else
{
uint8_t v___x_5126_; 
v___x_5126_ = 0;
return v___x_5126_;
}
}
else
{
if (lean_obj_tag(v_x_5124_) == 0)
{
uint8_t v___x_5127_; 
v___x_5127_ = 0;
return v___x_5127_;
}
else
{
lean_object* v_val_5128_; lean_object* v_val_5129_; uint8_t v___x_5130_; 
v_val_5128_ = lean_ctor_get(v_x_5123_, 0);
v_val_5129_ = lean_ctor_get(v_x_5124_, 0);
v___x_5130_ = lean_level_eq(v_val_5128_, v_val_5129_);
return v___x_5130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5131_, lean_object* v_x_5132_){
_start:
{
uint8_t v_res_5133_; lean_object* v_r_5134_; 
v_res_5133_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5131_, v_x_5132_);
lean_dec(v_x_5132_);
lean_dec(v_x_5131_);
v_r_5134_ = lean_box(v_res_5133_);
return v_r_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5154_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5146_ = v___x_5143_;
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5143_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5148_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5149_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5144_, v___x_5148_);
lean_dec(v_a_5144_);
v___x_5150_ = lean_box(v___x_5149_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5150_);
v___x_5152_ = v___x_5146_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5150_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
v_a_5155_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5143_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5143_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_Meta_isPropFormerType(v_type_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v___x_5176_; 
lean_inc(v_a_5174_);
lean_inc_ref(v_a_5173_);
lean_inc(v_a_5172_);
lean_inc_ref(v_a_5171_);
v___x_5176_ = lean_infer_type(v_e_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_object* v_a_5177_; lean_object* v___x_5178_; 
v_a_5177_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_a_5177_);
lean_dec_ref_known(v___x_5176_, 1);
v___x_5178_ = l_Lean_Meta_isTypeFormerType(v_a_5177_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
return v___x_5178_;
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
v_a_5179_ = lean_ctor_get(v___x_5176_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5176_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5176_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5176_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Lean_Meta_isTypeFormer(v_e_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5194_, lean_object* v_maxFVars_x3f_5195_, lean_object* v_k_5196_, uint8_t v_cleanupAnnotations_5197_, uint8_t v_whnfType_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v___f_5204_; lean_object* v___x_5205_; 
v___f_5204_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5204_, 0, v_k_5196_);
v___x_5205_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5194_, v_maxFVars_x3f_5195_, v___f_5204_, v_cleanupAnnotations_5197_, v_whnfType_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5205_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5205_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
v_a_5214_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5205_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5205_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5222_, lean_object* v_maxFVars_x3f_5223_, lean_object* v_k_5224_, lean_object* v_cleanupAnnotations_5225_, lean_object* v_whnfType_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5232_; uint8_t v_whnfType_boxed_5233_; lean_object* v_res_5234_; 
v_cleanupAnnotations_boxed_5232_ = lean_unbox(v_cleanupAnnotations_5225_);
v_whnfType_boxed_5233_ = lean_unbox(v_whnfType_5226_);
v_res_5234_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5222_, v_maxFVars_x3f_5223_, v_k_5224_, v_cleanupAnnotations_boxed_5232_, v_whnfType_boxed_5233_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5235_, lean_object* v_type_5236_, lean_object* v_maxFVars_x3f_5237_, lean_object* v_k_5238_, uint8_t v_cleanupAnnotations_5239_, uint8_t v_whnfType_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5236_, v_maxFVars_x3f_5237_, v_k_5238_, v_cleanupAnnotations_5239_, v_whnfType_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_type_5248_, lean_object* v_maxFVars_x3f_5249_, lean_object* v_k_5250_, lean_object* v_cleanupAnnotations_5251_, lean_object* v_whnfType_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5258_; uint8_t v_whnfType_boxed_5259_; lean_object* v_res_5260_; 
v_cleanupAnnotations_boxed_5258_ = lean_unbox(v_cleanupAnnotations_5251_);
v_whnfType_boxed_5259_ = lean_unbox(v_whnfType_5252_);
v_res_5260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5247_, v_type_5248_, v_maxFVars_x3f_5249_, v_k_5250_, v_cleanupAnnotations_boxed_5258_, v_whnfType_boxed_5259_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
return v_res_5260_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5261_, lean_object* v_as_5262_, size_t v_i_5263_, size_t v_stop_5264_){
_start:
{
uint8_t v___x_5265_; 
v___x_5265_ = lean_usize_dec_eq(v_i_5263_, v_stop_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; uint8_t v___x_5267_; 
v___x_5266_ = lean_array_uget_borrowed(v_as_5262_, v_i_5263_);
v___x_5267_ = lean_expr_eqv(v_a_5261_, v___x_5266_);
if (v___x_5267_ == 0)
{
size_t v___x_5268_; size_t v___x_5269_; 
v___x_5268_ = ((size_t)1ULL);
v___x_5269_ = lean_usize_add(v_i_5263_, v___x_5268_);
v_i_5263_ = v___x_5269_;
goto _start;
}
else
{
return v___x_5267_;
}
}
else
{
uint8_t v___x_5271_; 
v___x_5271_ = 0;
return v___x_5271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5272_, lean_object* v_as_5273_, lean_object* v_i_5274_, lean_object* v_stop_5275_){
_start:
{
size_t v_i_boxed_5276_; size_t v_stop_boxed_5277_; uint8_t v_res_5278_; lean_object* v_r_5279_; 
v_i_boxed_5276_ = lean_unbox_usize(v_i_5274_);
lean_dec(v_i_5274_);
v_stop_boxed_5277_ = lean_unbox_usize(v_stop_5275_);
lean_dec(v_stop_5275_);
v_res_5278_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5272_, v_as_5273_, v_i_boxed_5276_, v_stop_boxed_5277_);
lean_dec_ref(v_as_5273_);
lean_dec_ref(v_a_5272_);
v_r_5279_ = lean_box(v_res_5278_);
return v_r_5279_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; uint8_t v___x_5284_; 
v___x_5282_ = lean_unsigned_to_nat(0u);
v___x_5283_ = lean_array_get_size(v_as_5280_);
v___x_5284_ = lean_nat_dec_lt(v___x_5282_, v___x_5283_);
if (v___x_5284_ == 0)
{
return v___x_5284_;
}
else
{
if (v___x_5284_ == 0)
{
return v___x_5284_;
}
else
{
size_t v___x_5285_; size_t v___x_5286_; uint8_t v___x_5287_; 
v___x_5285_ = ((size_t)0ULL);
v___x_5286_ = lean_usize_of_nat(v___x_5283_);
v___x_5287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5281_, v_as_5280_, v___x_5285_, v___x_5286_);
return v___x_5287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5288_, lean_object* v_a_5289_){
_start:
{
uint8_t v_res_5290_; lean_object* v_r_5291_; 
v_res_5290_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5288_, v_a_5289_);
lean_dec_ref(v_a_5289_);
lean_dec_ref(v_as_5288_);
v_r_5291_ = lean_box(v_res_5290_);
return v_r_5291_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5292_, lean_object* v_e_5293_){
_start:
{
uint8_t v___x_5294_; uint8_t v___x_5295_; 
v___x_5294_ = l_Lean_Expr_hasFVar(v_e_5293_);
v___x_5295_ = lean_bool_not(v___x_5294_);
if (v___x_5295_ == 0)
{
uint8_t v___x_5296_; lean_object* v_d_5298_; lean_object* v_b_5299_; 
v___x_5296_ = 1;
switch(lean_obj_tag(v_e_5293_))
{
case 7:
{
lean_object* v_binderType_5302_; lean_object* v_body_5303_; 
v_binderType_5302_ = lean_ctor_get(v_e_5293_, 1);
lean_inc_ref(v_binderType_5302_);
v_body_5303_ = lean_ctor_get(v_e_5293_, 2);
lean_inc_ref(v_body_5303_);
lean_dec_ref_known(v_e_5293_, 3);
v_d_5298_ = v_binderType_5302_;
v_b_5299_ = v_body_5303_;
goto v___jp_5297_;
}
case 6:
{
lean_object* v_binderType_5304_; lean_object* v_body_5305_; 
v_binderType_5304_ = lean_ctor_get(v_e_5293_, 1);
lean_inc_ref(v_binderType_5304_);
v_body_5305_ = lean_ctor_get(v_e_5293_, 2);
lean_inc_ref(v_body_5305_);
lean_dec_ref_known(v_e_5293_, 3);
v_d_5298_ = v_binderType_5304_;
v_b_5299_ = v_body_5305_;
goto v___jp_5297_;
}
case 10:
{
lean_object* v_expr_5306_; 
v_expr_5306_ = lean_ctor_get(v_e_5293_, 1);
lean_inc_ref(v_expr_5306_);
lean_dec_ref_known(v_e_5293_, 2);
v_e_5293_ = v_expr_5306_;
goto _start;
}
case 8:
{
lean_object* v_type_5308_; lean_object* v_value_5309_; lean_object* v_body_5310_; uint8_t v___x_5311_; 
v_type_5308_ = lean_ctor_get(v_e_5293_, 1);
lean_inc_ref(v_type_5308_);
v_value_5309_ = lean_ctor_get(v_e_5293_, 2);
lean_inc_ref(v_value_5309_);
v_body_5310_ = lean_ctor_get(v_e_5293_, 3);
lean_inc_ref(v_body_5310_);
lean_dec_ref_known(v_e_5293_, 4);
v___x_5311_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5292_, v_type_5308_);
if (v___x_5311_ == 0)
{
uint8_t v___x_5312_; 
v___x_5312_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5292_, v_value_5309_);
if (v___x_5312_ == 0)
{
v_e_5293_ = v_body_5310_;
goto _start;
}
else
{
lean_dec_ref(v_body_5310_);
return v___x_5296_;
}
}
else
{
lean_dec_ref(v_body_5310_);
lean_dec_ref(v_value_5309_);
return v___x_5296_;
}
}
case 5:
{
lean_object* v_fn_5314_; lean_object* v_arg_5315_; uint8_t v___x_5316_; 
v_fn_5314_ = lean_ctor_get(v_e_5293_, 0);
lean_inc_ref(v_fn_5314_);
v_arg_5315_ = lean_ctor_get(v_e_5293_, 1);
lean_inc_ref(v_arg_5315_);
lean_dec_ref_known(v_e_5293_, 2);
v___x_5316_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5292_, v_fn_5314_);
if (v___x_5316_ == 0)
{
v_e_5293_ = v_arg_5315_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5315_);
return v___x_5296_;
}
}
case 11:
{
lean_object* v_struct_5318_; 
v_struct_5318_ = lean_ctor_get(v_e_5293_, 2);
lean_inc_ref(v_struct_5318_);
lean_dec_ref_known(v_e_5293_, 3);
v_e_5293_ = v_struct_5318_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5320_; lean_object* v___x_5321_; uint8_t v___x_5322_; 
v_fvarId_5320_ = lean_ctor_get(v_e_5293_, 0);
lean_inc(v_fvarId_5320_);
lean_dec_ref_known(v_e_5293_, 1);
v___x_5321_ = l_Lean_Expr_fvar___override(v_fvarId_5320_);
v___x_5322_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5292_, v___x_5321_);
lean_dec_ref(v___x_5321_);
return v___x_5322_;
}
default: 
{
lean_dec_ref(v_e_5293_);
return v___x_5295_;
}
}
v___jp_5297_:
{
uint8_t v___x_5300_; 
v___x_5300_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5292_, v_d_5298_);
if (v___x_5300_ == 0)
{
v_e_5293_ = v_b_5299_;
goto _start;
}
else
{
lean_dec_ref(v_b_5299_);
return v___x_5296_;
}
}
}
else
{
uint8_t v___x_5323_; 
lean_dec_ref(v_e_5293_);
v___x_5323_ = 0;
return v___x_5323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5324_, lean_object* v_e_5325_){
_start:
{
uint8_t v_res_5326_; lean_object* v_r_5327_; 
v_res_5326_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5324_, v_e_5325_);
lean_dec_ref(v_xs_5324_);
v_r_5327_ = lean_box(v_res_5326_);
return v_r_5327_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5330_ = l_Lean_stringToMessageData(v___x_5329_);
return v___x_5330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5333_ = l_Lean_stringToMessageData(v___x_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5334_, lean_object* v_type_5335_, lean_object* v_as_5336_, size_t v_sz_5337_, size_t v_i_5338_, lean_object* v_b_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v_a_5346_; uint8_t v___x_5350_; 
v___x_5350_ = lean_usize_dec_lt(v_i_5338_, v_sz_5337_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
lean_dec_ref(v_type_5335_);
v___x_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5351_, 0, v_b_5339_);
return v___x_5351_;
}
else
{
lean_object* v___x_5352_; lean_object* v_a_5353_; uint8_t v___x_5354_; 
v___x_5352_ = lean_box(0);
v_a_5353_ = lean_array_uget_borrowed(v_as_5336_, v_i_5338_);
lean_inc(v_a_5353_);
v___x_5354_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5334_, v_a_5353_);
if (v___x_5354_ == 0)
{
v_a_5346_ = v___x_5352_;
goto v___jp_5345_;
}
else
{
lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5355_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5353_);
v___x_5356_ = l_Lean_MessageData_ofExpr(v_a_5353_);
v___x_5357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5355_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
v___x_5358_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5357_);
lean_ctor_set(v___x_5359_, 1, v___x_5358_);
lean_inc_ref(v_type_5335_);
v___x_5360_ = l_Lean_MessageData_ofExpr(v_type_5335_);
v___x_5361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5359_);
lean_ctor_set(v___x_5361_, 1, v___x_5360_);
v___x_5362_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5361_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_dec_ref_known(v___x_5362_, 1);
v_a_5346_ = v___x_5352_;
goto v___jp_5345_;
}
else
{
lean_dec_ref(v_type_5335_);
return v___x_5362_;
}
}
}
v___jp_5345_:
{
size_t v___x_5347_; size_t v___x_5348_; 
v___x_5347_ = ((size_t)1ULL);
v___x_5348_ = lean_usize_add(v_i_5338_, v___x_5347_);
v_i_5338_ = v___x_5348_;
v_b_5339_ = v_a_5346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5363_, lean_object* v_type_5364_, lean_object* v_as_5365_, lean_object* v_sz_5366_, lean_object* v_i_5367_, lean_object* v_b_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
size_t v_sz_boxed_5374_; size_t v_i_boxed_5375_; lean_object* v_res_5376_; 
v_sz_boxed_5374_ = lean_unbox_usize(v_sz_5366_);
lean_dec(v_sz_5366_);
v_i_boxed_5375_ = lean_unbox_usize(v_i_5367_);
lean_dec(v_i_5367_);
v_res_5376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5363_, v_type_5364_, v_as_5365_, v_sz_boxed_5374_, v_i_boxed_5375_, v_b_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec_ref(v_as_5365_);
lean_dec_ref(v_xs_5363_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5377_, size_t v_i_5378_, lean_object* v_bs_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
uint8_t v___x_5385_; 
v___x_5385_ = lean_usize_dec_lt(v_i_5378_, v_sz_5377_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
v___x_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5386_, 0, v_bs_5379_);
return v___x_5386_;
}
else
{
lean_object* v_v_5387_; lean_object* v___x_5388_; 
v_v_5387_ = lean_array_uget_borrowed(v_bs_5379_, v_i_5378_);
lean_inc(v___y_5383_);
lean_inc_ref(v___y_5382_);
lean_inc(v___y_5381_);
lean_inc_ref(v___y_5380_);
lean_inc(v_v_5387_);
v___x_5388_ = lean_infer_type(v_v_5387_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
if (lean_obj_tag(v___x_5388_) == 0)
{
lean_object* v_a_5389_; lean_object* v___x_5390_; lean_object* v_bs_x27_5391_; size_t v___x_5392_; size_t v___x_5393_; lean_object* v___x_5394_; 
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc(v_a_5389_);
lean_dec_ref_known(v___x_5388_, 1);
v___x_5390_ = lean_unsigned_to_nat(0u);
v_bs_x27_5391_ = lean_array_uset(v_bs_5379_, v_i_5378_, v___x_5390_);
v___x_5392_ = ((size_t)1ULL);
v___x_5393_ = lean_usize_add(v_i_5378_, v___x_5392_);
v___x_5394_ = lean_array_uset(v_bs_x27_5391_, v_i_5378_, v_a_5389_);
v_i_5378_ = v___x_5393_;
v_bs_5379_ = v___x_5394_;
goto _start;
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec_ref(v_bs_5379_);
v_a_5396_ = lean_ctor_get(v___x_5388_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5388_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5388_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5404_, lean_object* v_i_5405_, lean_object* v_bs_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
size_t v_sz_boxed_5412_; size_t v_i_boxed_5413_; lean_object* v_res_5414_; 
v_sz_boxed_5412_ = lean_unbox_usize(v_sz_5404_);
lean_dec(v_sz_5404_);
v_i_boxed_5413_ = lean_unbox_usize(v_i_5405_);
lean_dec(v_i_5405_);
v_res_5414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5412_, v_i_boxed_5413_, v_bs_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5414_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5417_ = l_Lean_stringToMessageData(v___x_5416_);
return v___x_5417_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5420_ = l_Lean_stringToMessageData(v___x_5419_);
return v___x_5420_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5422_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5423_ = l_Lean_stringToMessageData(v___x_5422_);
return v___x_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5424_, lean_object* v_n_5425_, lean_object* v_xs_5426_, lean_object* v_x_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5457_; uint8_t v___x_5458_; 
v___x_5457_ = lean_array_get_size(v_xs_5426_);
v___x_5458_ = lean_nat_dec_eq(v___x_5457_, v_n_5425_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
lean_dec_ref(v_xs_5426_);
v___x_5459_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5460_ = l_Lean_MessageData_ofExpr(v_type_5424_);
v___x_5461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5459_);
lean_ctor_set(v___x_5461_, 1, v___x_5460_);
v___x_5462_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5461_);
lean_ctor_set(v___x_5463_, 1, v___x_5462_);
v___x_5464_ = l_Nat_reprFast(v_n_5425_);
v___x_5465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5464_);
v___x_5466_ = l_Lean_MessageData_ofFormat(v___x_5465_);
v___x_5467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5467_, 0, v___x_5463_);
lean_ctor_set(v___x_5467_, 1, v___x_5466_);
v___x_5468_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5467_);
lean_ctor_set(v___x_5469_, 1, v___x_5468_);
v___x_5470_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5469_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5470_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5470_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
else
{
lean_dec(v_n_5425_);
goto v___jp_5433_;
}
v___jp_5433_:
{
size_t v_sz_5434_; size_t v___x_5435_; lean_object* v___x_5436_; 
v_sz_5434_ = lean_array_size(v_xs_5426_);
v___x_5435_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5426_);
v___x_5436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5434_, v___x_5435_, v_xs_5426_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5438_; size_t v_sz_5439_; lean_object* v___x_5440_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = lean_box(0);
v_sz_5439_ = lean_array_size(v_a_5437_);
v___x_5440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5426_, v_type_5424_, v_a_5437_, v_sz_5439_, v___x_5435_, v___x_5438_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
lean_dec_ref(v_xs_5426_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5447_ == 0)
{
lean_object* v_unused_5448_; 
v_unused_5448_ = lean_ctor_get(v___x_5440_, 0);
lean_dec(v_unused_5448_);
v___x_5442_ = v___x_5440_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_dec(v___x_5440_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 0, v_a_5437_);
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5437_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
else
{
lean_object* v_a_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5456_; 
lean_dec(v_a_5437_);
v_a_5449_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5451_ = v___x_5440_;
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_a_5449_);
lean_dec(v___x_5440_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5454_; 
if (v_isShared_5452_ == 0)
{
v___x_5454_ = v___x_5451_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5449_);
v___x_5454_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
return v___x_5454_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5426_);
lean_dec_ref(v_type_5424_);
return v___x_5436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5479_, lean_object* v_n_5480_, lean_object* v_xs_5481_, lean_object* v_x_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5479_, v_n_5480_, v_xs_5481_, v_x_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_x_5482_);
return v_res_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5489_, lean_object* v_type_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_){
_start:
{
lean_object* v___f_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; lean_object* v___x_5499_; 
lean_inc(v_n_5489_);
lean_inc_ref(v_type_5490_);
v___f_5496_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5496_, 0, v_type_5490_);
lean_closure_set(v___f_5496_, 1, v_n_5489_);
v___x_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5497_, 0, v_n_5489_);
v___x_5498_ = 0;
v___x_5499_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5490_, v___x_5497_, v___f_5496_, v___x_5498_, v___x_5498_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5500_, lean_object* v_type_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_){
_start:
{
lean_object* v_res_5507_; 
v_res_5507_ = l_Lean_Meta_arrowDomainsN(v_n_5500_, v_type_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_);
lean_dec(v_a_5505_);
lean_dec_ref(v_a_5504_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
return v_res_5507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5508_, lean_object* v_e_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_){
_start:
{
lean_object* v___x_5515_; 
lean_inc(v_a_5513_);
lean_inc_ref(v_a_5512_);
lean_inc(v_a_5511_);
lean_inc_ref(v_a_5510_);
v___x_5515_ = lean_infer_type(v_e_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_);
if (lean_obj_tag(v___x_5515_) == 0)
{
lean_object* v_a_5516_; lean_object* v___x_5517_; 
v_a_5516_ = lean_ctor_get(v___x_5515_, 0);
lean_inc(v_a_5516_);
lean_dec_ref_known(v___x_5515_, 1);
v___x_5517_ = l_Lean_Meta_arrowDomainsN(v_n_5508_, v_a_5516_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_);
return v___x_5517_;
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec(v_n_5508_);
v_a_5518_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5515_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5515_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5526_, lean_object* v_e_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l_Lean_Meta_inferArgumentTypesN(v_n_5526_, v_e_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_a_5531_);
lean_dec_ref(v_a_5530_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
return v_res_5533_;
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
