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
size_t lean_usize_shift_left(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2;
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
v___x_313_ = lean_unsigned_to_nat(1838u);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; 
v___x_1755_ = ((size_t)5ULL);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_shift_left(v___x_1756_, v___x_1755_);
return v___x_1757_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; 
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1760_ = lean_usize_sub(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1762_, size_t v_x_1763_, size_t v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 0)
{
lean_object* v_es_1767_; size_t v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; lean_object* v_j_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_es_1767_ = lean_ctor_get(v_x_1762_, 0);
v___x_1768_ = ((size_t)5ULL);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1771_ = lean_usize_land(v_x_1763_, v___x_1770_);
v_j_1772_ = lean_usize_to_nat(v___x_1771_);
v___x_1773_ = lean_array_get_size(v_es_1767_);
v___x_1774_ = lean_nat_dec_lt(v_j_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec(v_j_1772_);
lean_dec(v_x_1766_);
lean_dec(v_x_1765_);
return v_x_1762_;
}
else
{
lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1811_; 
lean_inc_ref(v_es_1767_);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1762_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; 
v_unused_1812_ = lean_ctor_get(v_x_1762_, 0);
lean_dec(v_unused_1812_);
v___x_1776_ = v_x_1762_;
v_isShared_1777_ = v_isSharedCheck_1811_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v_x_1762_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1811_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_v_1778_; lean_object* v___x_1779_; lean_object* v_xs_x27_1780_; lean_object* v___y_1782_; 
v_v_1778_ = lean_array_fget(v_es_1767_, v_j_1772_);
v___x_1779_ = lean_box(0);
v_xs_x27_1780_ = lean_array_fset(v_es_1767_, v_j_1772_, v___x_1779_);
switch(lean_obj_tag(v_v_1778_))
{
case 0:
{
lean_object* v_key_1787_; lean_object* v_val_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_key_1787_ = lean_ctor_get(v_v_1778_, 0);
v_val_1788_ = lean_ctor_get(v_v_1778_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_v_1778_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1790_ = v_v_1778_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_val_1788_);
lean_inc(v_key_1787_);
lean_dec(v_v_1778_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Lean_instBEqMVarId_beq(v_x_1765_, v_key_1787_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_del_object(v___x_1790_);
v___x_1793_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1787_, v_val_1788_, v_x_1765_, v_x_1766_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___y_1782_ = v___x_1794_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1796_; 
lean_dec(v_val_1788_);
lean_dec(v_key_1787_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v_x_1766_);
lean_ctor_set(v___x_1790_, 0, v_x_1765_);
v___x_1796_ = v___x_1790_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_x_1765_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_x_1766_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1782_ = v___x_1796_;
goto v___jp_1781_;
}
}
}
}
case 1:
{
lean_object* v_node_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1809_; 
v_node_1799_ = lean_ctor_get(v_v_1778_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_v_1778_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1801_ = v_v_1778_;
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_node_1799_);
lean_dec(v_v_1778_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1803_ = lean_usize_shift_right(v_x_1763_, v___x_1768_);
v___x_1804_ = lean_usize_add(v_x_1764_, v___x_1769_);
v___x_1805_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1799_, v___x_1803_, v___x_1804_, v_x_1765_, v_x_1766_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1805_);
v___x_1807_ = v___x_1801_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
v___y_1782_ = v___x_1807_;
goto v___jp_1781_;
}
}
}
default: 
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_x_1765_);
lean_ctor_set(v___x_1810_, 1, v_x_1766_);
v___y_1782_ = v___x_1810_;
goto v___jp_1781_;
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_array_fset(v_xs_x27_1780_, v_j_1772_, v___y_1782_);
lean_dec(v_j_1772_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1783_);
v___x_1785_ = v___x_1776_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
lean_object* v_ks_1813_; lean_object* v_vs_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1834_; 
v_ks_1813_ = lean_ctor_get(v_x_1762_, 0);
v_vs_1814_ = lean_ctor_get(v_x_1762_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1762_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1816_ = v_x_1762_;
v_isShared_1817_ = v_isSharedCheck_1834_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_vs_1814_);
lean_inc(v_ks_1813_);
lean_dec(v_x_1762_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1834_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_ks_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_vs_1814_);
v___x_1819_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v_newNode_1820_; uint8_t v___y_1822_; size_t v___x_1828_; uint8_t v___x_1829_; 
v_newNode_1820_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1819_, v_x_1765_, v_x_1766_);
v___x_1828_ = ((size_t)7ULL);
v___x_1829_ = lean_usize_dec_le(v___x_1828_, v_x_1764_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1820_);
v___x_1831_ = lean_unsigned_to_nat(4u);
v___x_1832_ = lean_nat_dec_lt(v___x_1830_, v___x_1831_);
lean_dec(v___x_1830_);
v___y_1822_ = v___x_1832_;
goto v___jp_1821_;
}
else
{
v___y_1822_ = v___x_1829_;
goto v___jp_1821_;
}
v___jp_1821_:
{
if (v___y_1822_ == 0)
{
lean_object* v_ks_1823_; lean_object* v_vs_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_ks_1823_ = lean_ctor_get(v_newNode_1820_, 0);
lean_inc_ref(v_ks_1823_);
v_vs_1824_ = lean_ctor_get(v_newNode_1820_, 1);
lean_inc_ref(v_vs_1824_);
lean_dec_ref(v_newNode_1820_);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1764_, v_ks_1823_, v_vs_1824_, v___x_1825_, v___x_1826_);
lean_dec_ref(v_vs_1824_);
lean_dec_ref(v_ks_1823_);
return v___x_1827_;
}
else
{
return v_newNode_1820_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1835_, lean_object* v_keys_1836_, lean_object* v_vals_1837_, lean_object* v_i_1838_, lean_object* v_entries_1839_){
_start:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_array_get_size(v_keys_1836_);
v___x_1841_ = lean_nat_dec_lt(v_i_1838_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_dec(v_i_1838_);
return v_entries_1839_;
}
else
{
lean_object* v_k_1842_; lean_object* v_v_1843_; uint64_t v___x_1844_; size_t v_h_1845_; size_t v___x_1846_; lean_object* v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; size_t v_h_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_k_1842_ = lean_array_fget_borrowed(v_keys_1836_, v_i_1838_);
v_v_1843_ = lean_array_fget_borrowed(v_vals_1837_, v_i_1838_);
v___x_1844_ = l_Lean_instHashableMVarId_hash(v_k_1842_);
v_h_1845_ = lean_uint64_to_usize(v___x_1844_);
v___x_1846_ = ((size_t)5ULL);
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_sub(v_depth_1835_, v___x_1848_);
v___x_1850_ = lean_usize_mul(v___x_1846_, v___x_1849_);
v_h_1851_ = lean_usize_shift_right(v_h_1845_, v___x_1850_);
v___x_1852_ = lean_nat_add(v_i_1838_, v___x_1847_);
lean_dec(v_i_1838_);
lean_inc(v_v_1843_);
lean_inc(v_k_1842_);
v___x_1853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1839_, v_h_1851_, v_depth_1835_, v_k_1842_, v_v_1843_);
v_i_1838_ = v___x_1852_;
v_entries_1839_ = v___x_1853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1855_, lean_object* v_keys_1856_, lean_object* v_vals_1857_, lean_object* v_i_1858_, lean_object* v_entries_1859_){
_start:
{
size_t v_depth_boxed_1860_; lean_object* v_res_1861_; 
v_depth_boxed_1860_ = lean_unbox_usize(v_depth_1855_);
lean_dec(v_depth_1855_);
v_res_1861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1860_, v_keys_1856_, v_vals_1857_, v_i_1858_, v_entries_1859_);
lean_dec_ref(v_vals_1857_);
lean_dec_ref(v_keys_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
size_t v_x_1244__boxed_1867_; size_t v_x_1245__boxed_1868_; lean_object* v_res_1869_; 
v_x_1244__boxed_1867_ = lean_unbox_usize(v_x_1863_);
lean_dec(v_x_1863_);
v_x_1245__boxed_1868_ = lean_unbox_usize(v_x_1864_);
lean_dec(v_x_1864_);
v_res_1869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1862_, v_x_1244__boxed_1867_, v_x_1245__boxed_1868_, v_x_1865_, v_x_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
uint64_t v___x_1873_; size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = l_Lean_instHashableMVarId_hash(v_x_1871_);
v___x_1874_ = lean_uint64_to_usize(v___x_1873_);
v___x_1875_ = ((size_t)1ULL);
v___x_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1870_, v___x_1874_, v___x_1875_, v_x_1871_, v_x_1872_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1877_, lean_object* v_val_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v_mctx_1882_; lean_object* v_cache_1883_; lean_object* v_zetaDeltaFVarIds_1884_; lean_object* v_postponed_1885_; lean_object* v_diag_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1914_; 
v___x_1881_ = lean_st_ref_take(v___y_1879_);
v_mctx_1882_ = lean_ctor_get(v___x_1881_, 0);
v_cache_1883_ = lean_ctor_get(v___x_1881_, 1);
v_zetaDeltaFVarIds_1884_ = lean_ctor_get(v___x_1881_, 2);
v_postponed_1885_ = lean_ctor_get(v___x_1881_, 3);
v_diag_1886_ = lean_ctor_get(v___x_1881_, 4);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1888_ = v___x_1881_;
v_isShared_1889_ = v_isSharedCheck_1914_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_diag_1886_);
lean_inc(v_postponed_1885_);
lean_inc(v_zetaDeltaFVarIds_1884_);
lean_inc(v_cache_1883_);
lean_inc(v_mctx_1882_);
lean_dec(v___x_1881_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1914_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_depth_1890_; lean_object* v_levelAssignDepth_1891_; lean_object* v_lmvarCounter_1892_; lean_object* v_mvarCounter_1893_; lean_object* v_lDecls_1894_; lean_object* v_decls_1895_; lean_object* v_userNames_1896_; lean_object* v_lAssignment_1897_; lean_object* v_eAssignment_1898_; lean_object* v_dAssignment_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1913_; 
v_depth_1890_ = lean_ctor_get(v_mctx_1882_, 0);
v_levelAssignDepth_1891_ = lean_ctor_get(v_mctx_1882_, 1);
v_lmvarCounter_1892_ = lean_ctor_get(v_mctx_1882_, 2);
v_mvarCounter_1893_ = lean_ctor_get(v_mctx_1882_, 3);
v_lDecls_1894_ = lean_ctor_get(v_mctx_1882_, 4);
v_decls_1895_ = lean_ctor_get(v_mctx_1882_, 5);
v_userNames_1896_ = lean_ctor_get(v_mctx_1882_, 6);
v_lAssignment_1897_ = lean_ctor_get(v_mctx_1882_, 7);
v_eAssignment_1898_ = lean_ctor_get(v_mctx_1882_, 8);
v_dAssignment_1899_ = lean_ctor_get(v_mctx_1882_, 9);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_mctx_1882_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1901_ = v_mctx_1882_;
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_dAssignment_1899_);
lean_inc(v_eAssignment_1898_);
lean_inc(v_lAssignment_1897_);
lean_inc(v_userNames_1896_);
lean_inc(v_decls_1895_);
lean_inc(v_lDecls_1894_);
lean_inc(v_mvarCounter_1893_);
lean_inc(v_lmvarCounter_1892_);
lean_inc(v_levelAssignDepth_1891_);
lean_inc(v_depth_1890_);
lean_dec(v_mctx_1882_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1898_, v_mvarId_1877_, v_val_1878_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 8, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_depth_1890_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_levelAssignDepth_1891_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_lmvarCounter_1892_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_mvarCounter_1893_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_lDecls_1894_);
lean_ctor_set(v_reuseFailAlloc_1912_, 5, v_decls_1895_);
lean_ctor_set(v_reuseFailAlloc_1912_, 6, v_userNames_1896_);
lean_ctor_set(v_reuseFailAlloc_1912_, 7, v_lAssignment_1897_);
lean_ctor_set(v_reuseFailAlloc_1912_, 8, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1912_, 9, v_dAssignment_1899_);
v___x_1905_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1905_);
v___x_1907_ = v___x_1888_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_cache_1883_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_zetaDeltaFVarIds_1884_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_postponed_1885_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_diag_1886_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_st_ref_set(v___y_1879_, v___x_1907_);
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1915_, lean_object* v_val_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1915_, v_val_1916_, v___y_1917_);
lean_dec(v___y_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v___x_1926_; 
lean_inc(v_a_1924_);
lean_inc_ref(v_a_1923_);
lean_inc(v_a_1922_);
lean_inc_ref(v_a_1921_);
lean_inc_ref(v_type_1920_);
v___x_1926_ = lean_infer_type(v_type_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = l_Lean_Meta_whnfD(v_a_1927_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1963_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1963_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1963_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
switch(lean_obj_tag(v_a_1929_))
{
case 3:
{
lean_object* v_u_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_type_1920_);
v_u_1933_ = lean_ctor_get(v_a_1929_, 0);
lean_inc(v_u_1933_);
lean_dec_ref_known(v_a_1929_, 1);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_u_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_u_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
case 2:
{
lean_object* v_mvarId_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1931_);
v_mvarId_1937_ = lean_ctor_get(v_a_1929_, 0);
lean_inc_n(v_mvarId_1937_, 2);
lean_dec_ref_known(v_a_1929_, 1);
v___x_1938_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1937_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v_type_1920_);
v___x_1941_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_n(v_a_1942_, 2);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = l_Lean_mkSort(v_a_1942_);
v___x_1944_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1937_, v___x_1943_, v_a_1922_);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1944_, 0);
lean_dec(v_unused_1952_);
v___x_1946_ = v___x_1944_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v___x_1944_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_a_1942_);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1942_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_dec(v_mvarId_1937_);
return v___x_1941_;
}
}
else
{
lean_object* v___x_1953_; 
lean_dec(v_mvarId_1937_);
v___x_1953_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
return v___x_1953_;
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_mvarId_1937_);
lean_dec_ref(v_type_1920_);
v_a_1954_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1938_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1938_);
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
default: 
{
lean_object* v___x_1962_; 
lean_del_object(v___x_1931_);
lean_dec(v_a_1929_);
v___x_1962_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_type_1920_);
v_a_1964_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1928_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1928_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_type_1920_);
v_a_1972_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1926_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1926_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_getLevel(v_type_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1987_, lean_object* v_val_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1987_, v_val_1988_, v___y_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1995_, lean_object* v_val_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1995_, v_val_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2004_, v_x_2005_, v_x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2008_, lean_object* v_x_2009_, size_t v_x_2010_, size_t v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2009_, v_x_2010_, v_x_2011_, v_x_2012_, v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
size_t v_x_1603__boxed_2021_; size_t v_x_1604__boxed_2022_; lean_object* v_res_2023_; 
v_x_1603__boxed_2021_ = lean_unbox_usize(v_x_2017_);
lean_dec(v_x_2017_);
v_x_1604__boxed_2022_ = lean_unbox_usize(v_x_2018_);
lean_dec(v_x_2018_);
v_res_2023_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2015_, v_x_2016_, v_x_1603__boxed_2021_, v_x_1604__boxed_2022_, v_x_2019_, v_x_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2024_, lean_object* v_n_2025_, lean_object* v_k_2026_, lean_object* v_v_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2025_, v_k_2026_, v_v_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2029_, size_t v_depth_2030_, lean_object* v_keys_2031_, lean_object* v_vals_2032_, lean_object* v_heq_2033_, lean_object* v_i_2034_, lean_object* v_entries_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2030_, v_keys_2031_, v_vals_2032_, v_i_2034_, v_entries_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2037_, lean_object* v_depth_2038_, lean_object* v_keys_2039_, lean_object* v_vals_2040_, lean_object* v_heq_2041_, lean_object* v_i_2042_, lean_object* v_entries_2043_){
_start:
{
size_t v_depth_boxed_2044_; lean_object* v_res_2045_; 
v_depth_boxed_2044_ = lean_unbox_usize(v_depth_2038_);
lean_dec(v_depth_2038_);
v_res_2045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2037_, v_depth_boxed_2044_, v_keys_2039_, v_vals_2040_, v_heq_2041_, v_i_2042_, v_entries_2043_);
lean_dec_ref(v_vals_2040_);
lean_dec_ref(v_keys_2039_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2047_, v_x_2048_, v_x_2049_, v_x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2052_, lean_object* v_b_2053_, lean_object* v_c_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
lean_inc(v___y_2058_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
v___x_2060_ = lean_apply_7(v_k_2052_, v_b_2053_, v_c_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, lean_box(0));
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2061_, lean_object* v_b_2062_, lean_object* v_c_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2061_, v_b_2062_, v_c_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2070_, lean_object* v_k_2071_, uint8_t v_cleanupAnnotations_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___f_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2078_, 0, v_k_2071_);
v___x_2079_ = 0;
v___x_2080_ = lean_box(0);
v___x_2081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2079_, v___x_2080_, v_type_2070_, v___f_2078_, v_cleanupAnnotations_2072_, v___x_2079_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2081_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2081_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2098_, lean_object* v_k_2099_, lean_object* v_cleanupAnnotations_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2106_; lean_object* v_res_2107_; 
v_cleanupAnnotations_boxed_2106_ = lean_unbox(v_cleanupAnnotations_2100_);
v_res_2107_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2098_, v_k_2099_, v_cleanupAnnotations_boxed_2106_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2108_, lean_object* v_type_2109_, lean_object* v_k_2110_, uint8_t v_cleanupAnnotations_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2109_, v_k_2110_, v_cleanupAnnotations_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2118_, lean_object* v_type_2119_, lean_object* v_k_2120_, lean_object* v_cleanupAnnotations_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2127_; lean_object* v_res_2128_; 
v_cleanupAnnotations_boxed_2127_ = lean_unbox(v_cleanupAnnotations_2121_);
v_res_2128_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2118_, v_type_2119_, v_k_2120_, v_cleanupAnnotations_boxed_2127_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2129_, size_t v_i_2130_, size_t v_stop_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_usize_dec_eq(v_i_2130_, v_stop_2131_);
if (v___x_2138_ == 0)
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = ((size_t)1ULL);
v___x_2140_ = lean_usize_sub(v_i_2130_, v___x_2139_);
v___x_2141_ = lean_array_uget_borrowed(v_as_2129_, v___x_2140_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
lean_inc(v___x_2141_);
v___x_2142_ = lean_infer_type(v___x_2141_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_Meta_getLevel(v_a_2143_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_mkLevelIMax_x27(v_a_2145_, v_b_2132_);
v_i_2130_ = v___x_2140_;
v_b_2132_ = v___x_2146_;
goto _start;
}
else
{
lean_dec(v_b_2132_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2148_; 
v_a_2148_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2144_, 1);
v_i_2130_ = v___x_2140_;
v_b_2132_ = v_a_2148_;
goto _start;
}
else
{
return v___x_2144_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_b_2132_);
v_a_2150_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2142_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2142_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_b_2132_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2159_, lean_object* v_i_2160_, lean_object* v_stop_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
size_t v_i_boxed_2168_; size_t v_stop_boxed_2169_; lean_object* v_res_2170_; 
v_i_boxed_2168_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_stop_boxed_2169_ = lean_unbox_usize(v_stop_2161_);
lean_dec(v_stop_2161_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2159_, v_i_boxed_2168_, v_stop_boxed_2169_, v_b_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v_as_2159_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2171_, lean_object* v_e_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___y_2179_; lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Meta_getLevel(v_e_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
v___x_2200_ = lean_array_get_size(v_xs_2171_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_nat_dec_lt(v___x_2201_, v___x_2200_);
if (v___x_2202_ == 0)
{
lean_dec(v_a_2199_);
v___y_2179_ = v___x_2198_;
goto v___jp_2178_;
}
else
{
size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref_known(v___x_2198_, 1);
v___x_2203_ = lean_usize_of_nat(v___x_2200_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2171_, v___x_2203_, v___x_2204_, v_a_2199_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
v___y_2179_ = v___x_2205_;
goto v___jp_2178_;
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_a_2206_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2198_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2198_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
v___jp_2178_:
{
if (lean_obj_tag(v___y_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2189_; 
v_a_2180_ = lean_ctor_get(v___y_2179_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___y_2179_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2182_ = v___y_2179_;
v_isShared_2183_ = v_isSharedCheck_2189_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___y_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2189_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2184_ = l_Lean_Level_normalize(v_a_2180_);
lean_dec(v_a_2180_);
v___x_2185_ = l_Lean_mkSort(v___x_2184_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2185_);
v___x_2187_ = v___x_2182_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_a_2190_ = lean_ctor_get(v___y_2179_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___y_2179_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___y_2179_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___y_2179_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2214_, lean_object* v_e_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2214_, v_e_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v_xs_2214_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v___f_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; 
v___f_2229_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2230_ = 0;
v___x_2231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2223_, v___f_2229_, v___x_2230_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2239_, lean_object* v_k_2240_, uint8_t v_cleanupAnnotations_2241_, uint8_t v_preserveNondepLet_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___f_2248_; uint8_t v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2248_, 0, v_k_2240_);
v___x_2249_ = 1;
v___x_2250_ = 0;
v___x_2251_ = lean_box(0);
v___x_2252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2239_, v___x_2249_, v___x_2249_, v_preserveNondepLet_2242_, v___x_2250_, v___x_2251_, v___f_2248_, v_cleanupAnnotations_2241_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2252_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2252_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2269_, lean_object* v_k_2270_, lean_object* v_cleanupAnnotations_2271_, lean_object* v_preserveNondepLet_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2278_; uint8_t v_preserveNondepLet_boxed_2279_; lean_object* v_res_2280_; 
v_cleanupAnnotations_boxed_2278_ = lean_unbox(v_cleanupAnnotations_2271_);
v_preserveNondepLet_boxed_2279_ = lean_unbox(v_preserveNondepLet_2272_);
v_res_2280_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2269_, v_k_2270_, v_cleanupAnnotations_boxed_2278_, v_preserveNondepLet_boxed_2279_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2281_, lean_object* v_e_2282_, lean_object* v_k_2283_, uint8_t v_cleanupAnnotations_2284_, uint8_t v_preserveNondepLet_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2282_, v_k_2283_, v_cleanupAnnotations_2284_, v_preserveNondepLet_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_e_2293_, lean_object* v_k_2294_, lean_object* v_cleanupAnnotations_2295_, lean_object* v_preserveNondepLet_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2302_; uint8_t v_preserveNondepLet_boxed_2303_; lean_object* v_res_2304_; 
v_cleanupAnnotations_boxed_2302_ = lean_unbox(v_cleanupAnnotations_2295_);
v_preserveNondepLet_boxed_2303_ = lean_unbox(v_preserveNondepLet_2296_);
v_res_2304_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2292_, v_e_2293_, v_k_2294_, v_cleanupAnnotations_boxed_2302_, v_preserveNondepLet_boxed_2303_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2305_, lean_object* v_e_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
v___x_2312_ = lean_infer_type(v_e_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; uint8_t v___x_2314_; uint8_t v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = 0;
v___x_2315_ = 1;
v___x_2316_ = 1;
v___x_2317_ = l_Lean_Meta_mkForallFVars(v_xs_2305_, v_a_2313_, v___x_2314_, v___x_2315_, v___x_2314_, v___x_2316_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2317_;
}
else
{
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2318_, lean_object* v_e_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2318_, v_e_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_xs_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___f_2333_; uint8_t v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
v___f_2333_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2334_ = 0;
v___x_2335_ = 1;
v___x_2336_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2327_, v___f_2333_, v___x_2334_, v___x_2335_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2357_ = l_Lean_MessageData_ofName(v_mvarId_2350_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2360_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2369_, lean_object* v_mvarId_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2377_, lean_object* v_mvarId_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2377_, v_mvarId_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v_mctx_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_st_ref_get(v_a_2387_);
v_mctx_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_ref(v_mctx_2392_);
lean_dec(v___x_2391_);
v___x_2393_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2392_, v_mvarId_2385_);
lean_dec_ref(v_mctx_2392_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
return v___x_2394_;
}
else
{
lean_object* v_val_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_mvarId_2385_);
v_val_2395_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2397_ = v___x_2393_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_val_2395_);
lean_dec(v___x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_type_2399_; lean_object* v___x_2401_; 
v_type_2399_ = lean_ctor_get(v_val_2395_, 2);
lean_inc_ref(v_type_2399_);
lean_dec(v_val_2395_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 0);
lean_ctor_set(v___x_2397_, 0, v_type_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_type_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_lctx_2416_; lean_object* v___x_2417_; 
v_lctx_2416_ = lean_ctor_get(v_a_2412_, 2);
lean_inc(v_fvarId_2411_);
lean_inc_ref(v_lctx_2416_);
v___x_2417_ = lean_local_ctx_find(v_lctx_2416_, v_fvarId_2411_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2411_, v_a_2413_, v_a_2414_);
return v___x_2418_;
}
else
{
lean_object* v_val_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_fvarId_2411_);
v_val_2419_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2421_ = v___x_2417_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_val_2419_);
lean_dec(v___x_2417_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2423_ = l_Lean_LocalDecl_type(v_val_2419_);
lean_dec(v_val_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_a_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2434_, v_a_2435_, v_a_2437_, v_a_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_instMonadEIO(lean_box(0));
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2450_ = l_StateRefT_x27_instMonad___redArg(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2453_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___f_2455_; 
v___x_2454_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2455_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2455_, 0, v___x_2454_);
return v___f_2455_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___f_2457_; 
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2457_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2457_, 0, v___x_2456_);
return v___f_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; 
v___f_2458_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2459_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___f_2459_);
lean_ctor_set(v___x_2460_, 1, v___f_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___f_2462_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2462_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2462_, 0, v___x_2461_);
return v___f_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___f_2464_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2464_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2464_, 0, v___x_2463_);
return v___f_2464_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; 
v___f_2465_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2466_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___f_2466_);
lean_ctor_set(v___x_2467_, 1, v___f_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2470_, lean_object* v_inferType_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
uint8_t v_cacheInferType_2515_; 
v_cacheInferType_2515_ = lean_ctor_get_uint8(v_a_2472_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2515_ == 0)
{
lean_dec_ref(v_e_2470_);
goto v___jp_2477_;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = l_Lean_Expr_hasMVar(v_e_2470_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2470_, v_a_2472_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2618_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2618_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2618_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2564_; lean_object* v_cache_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2613_; 
v___x_2564_ = lean_st_ref_get(v_a_2473_);
v_cache_2565_ = lean_ctor_get(v___x_2564_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; lean_object* v_unused_2615_; lean_object* v_unused_2616_; lean_object* v_unused_2617_; 
v_unused_2614_ = lean_ctor_get(v___x_2564_, 4);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v___x_2564_, 3);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v___x_2564_, 2);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2617_);
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2613_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_cache_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2613_;
goto v_resetjp_2566_;
}
v___jp_2522_:
{
lean_object* v___x_2523_; 
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2523_ = lean_apply_5(v_inferType_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; uint8_t v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
v___x_2525_ = l_Lean_Expr_hasMVar(v_a_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2563_);
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2562_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v_cache_2530_; lean_object* v_mctx_2531_; lean_object* v_zetaDeltaFVarIds_2532_; lean_object* v_postponed_2533_; lean_object* v_diag_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2561_; 
v___x_2529_ = lean_st_ref_take(v_a_2473_);
v_cache_2530_ = lean_ctor_get(v___x_2529_, 1);
v_mctx_2531_ = lean_ctor_get(v___x_2529_, 0);
v_zetaDeltaFVarIds_2532_ = lean_ctor_get(v___x_2529_, 2);
v_postponed_2533_ = lean_ctor_get(v___x_2529_, 3);
v_diag_2534_ = lean_ctor_get(v___x_2529_, 4);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2536_ = v___x_2529_;
v_isShared_2537_ = v_isSharedCheck_2561_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_diag_2534_);
lean_inc(v_postponed_2533_);
lean_inc(v_zetaDeltaFVarIds_2532_);
lean_inc(v_cache_2530_);
lean_inc(v_mctx_2531_);
lean_dec(v___x_2529_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2561_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v_inferType_2538_; lean_object* v_funInfo_2539_; lean_object* v_synthInstance_2540_; lean_object* v_whnf_2541_; lean_object* v_defEqTrans_2542_; lean_object* v_defEqPerm_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2560_; 
v_inferType_2538_ = lean_ctor_get(v_cache_2530_, 0);
v_funInfo_2539_ = lean_ctor_get(v_cache_2530_, 1);
v_synthInstance_2540_ = lean_ctor_get(v_cache_2530_, 2);
v_whnf_2541_ = lean_ctor_get(v_cache_2530_, 3);
v_defEqTrans_2542_ = lean_ctor_get(v_cache_2530_, 4);
v_defEqPerm_2543_ = lean_ctor_get(v_cache_2530_, 5);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_cache_2530_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2545_ = v_cache_2530_;
v_isShared_2546_ = v_isSharedCheck_2560_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_defEqPerm_2543_);
lean_inc(v_defEqTrans_2542_);
lean_inc(v_whnf_2541_);
lean_inc(v_synthInstance_2540_);
lean_inc(v_funInfo_2539_);
lean_inc(v_inferType_2538_);
lean_dec(v_cache_2530_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2560_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___f_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___f_2547_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2524_);
v___x_2549_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2547_, v___x_2548_, v_inferType_2538_, v_a_2518_, v_a_2524_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2549_);
v___x_2551_ = v___x_2545_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_funInfo_2539_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_synthInstance_2540_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_whnf_2541_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_defEqTrans_2542_);
lean_ctor_set(v_reuseFailAlloc_2559_, 5, v_defEqPerm_2543_);
v___x_2551_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2553_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2551_);
v___x_2553_ = v___x_2536_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_mctx_2531_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_zetaDeltaFVarIds_2532_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_postponed_2533_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_diag_2534_);
v___x_2553_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_st_ref_set(v_a_2473_, v___x_2553_);
if (v_isShared_2528_ == 0)
{
v___x_2556_ = v___x_2527_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2524_);
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
lean_dec(v_a_2524_);
lean_dec(v_a_2518_);
return v___x_2523_;
}
}
else
{
lean_dec(v_a_2518_);
return v___x_2523_;
}
}
v_resetjp_2566_:
{
lean_object* v_inferType_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_inferType_2569_ = lean_ctor_get(v_cache_2565_, 0);
lean_inc_ref(v_inferType_2569_);
lean_dec_ref(v_cache_2565_);
v___f_2570_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2518_);
v___x_2572_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2570_, v___x_2571_, v_inferType_2569_, v_a_2518_);
lean_dec_ref(v_inferType_2569_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; lean_object* v_toApplicative_2574_; lean_object* v_toFunctor_2575_; lean_object* v_toSeq_2576_; lean_object* v_toSeqLeft_2577_; lean_object* v_toSeqRight_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___x_2588_; 
lean_del_object(v___x_2520_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2574_ = lean_ctor_get(v___x_2573_, 0);
v_toFunctor_2575_ = lean_ctor_get(v_toApplicative_2574_, 0);
v_toSeq_2576_ = lean_ctor_get(v_toApplicative_2574_, 2);
v_toSeqLeft_2577_ = lean_ctor_get(v_toApplicative_2574_, 3);
v_toSeqRight_2578_ = lean_ctor_get(v_toApplicative_2574_, 4);
v___f_2579_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2580_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2575_, 2);
v___f_2581_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2581_, 0, v_toFunctor_2575_);
v___f_2582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2582_, 0, v_toFunctor_2575_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___f_2581_);
lean_ctor_set(v___x_2583_, 1, v___f_2582_);
lean_inc(v_toSeqRight_2578_);
v___f_2584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2584_, 0, v_toSeqRight_2578_);
lean_inc(v_toSeqLeft_2577_);
v___f_2585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2585_, 0, v_toSeqLeft_2577_);
lean_inc(v_toSeq_2576_);
v___f_2586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2586_, 0, v_toSeq_2576_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v___f_2584_);
lean_ctor_set(v___x_2567_, 3, v___f_2585_);
lean_ctor_set(v___x_2567_, 2, v___f_2586_);
lean_ctor_set(v___x_2567_, 1, v___f_2579_);
lean_ctor_set(v___x_2567_, 0, v___x_2583_);
v___x_2588_ = v___x_2567_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___f_2579_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v___f_2586_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v___f_2585_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v___f_2584_);
v___x_2588_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v_cancelTk_x3f_2590_; 
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v___f_2580_);
v_cancelTk_x3f_2590_ = lean_ctor_get(v_a_2474_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2590_) == 1)
{
lean_object* v_val_2591_; uint8_t v___x_2592_; 
v_val_2591_ = lean_ctor_get(v_cancelTk_x3f_2590_, 0);
v___x_2592_ = l_IO_CancelToken_isSet(v_val_2591_);
if (v___x_2592_ == 0)
{
lean_dec_ref_known(v___x_2589_, 2);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2392__overap_2598_; lean_object* v___x_2599_; 
v___x_2593_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2594_ = l_Lean_Core_instMonadRefCoreM;
v___x_2595_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2596_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2595_, v___x_2589_);
v___x_2597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2593_);
lean_ctor_set(v___x_2597_, 1, v___x_2594_);
lean_ctor_set(v___x_2597_, 2, v___x_2596_);
v___x_2392__overap_2598_ = l_Lean_throwInterruptException___redArg(v___x_2597_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
v___x_2599_ = lean_apply_3(v___x_2392__overap_2598_, v_a_2474_, v_a_2475_, lean_box(0));
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_dec_ref_known(v___x_2599_, 1);
goto v___jp_2522_;
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2518_);
lean_dec_ref(v_inferType_2471_);
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
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
lean_dec_ref_known(v___x_2589_, 2);
goto v___jp_2522_;
}
}
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2611_; 
lean_del_object(v___x_2567_);
lean_dec(v_a_2518_);
lean_dec_ref(v_inferType_2471_);
v_val_2609_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v___x_2572_, 1);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_val_2609_);
v___x_2611_ = v___x_2520_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_val_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_inferType_2471_);
v_a_2619_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2517_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2517_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_dec_ref(v_e_2470_);
goto v___jp_2477_;
}
}
v___jp_2477_:
{
lean_object* v___x_2478_; lean_object* v_toApplicative_2479_; lean_object* v_toFunctor_2480_; lean_object* v_toSeq_2481_; lean_object* v_toSeqLeft_2482_; lean_object* v_toSeqRight_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_cancelTk_x3f_2494_; 
v___x_2478_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2479_ = lean_ctor_get(v___x_2478_, 0);
v_toFunctor_2480_ = lean_ctor_get(v_toApplicative_2479_, 0);
v_toSeq_2481_ = lean_ctor_get(v_toApplicative_2479_, 2);
v_toSeqLeft_2482_ = lean_ctor_get(v_toApplicative_2479_, 3);
v_toSeqRight_2483_ = lean_ctor_get(v_toApplicative_2479_, 4);
v___f_2484_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2485_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2480_, 2);
v___f_2486_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2486_, 0, v_toFunctor_2480_);
v___f_2487_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2487_, 0, v_toFunctor_2480_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___f_2486_);
lean_ctor_set(v___x_2488_, 1, v___f_2487_);
lean_inc(v_toSeqRight_2483_);
v___f_2489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2489_, 0, v_toSeqRight_2483_);
lean_inc(v_toSeqLeft_2482_);
v___f_2490_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2490_, 0, v_toSeqLeft_2482_);
lean_inc(v_toSeq_2481_);
v___f_2491_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2491_, 0, v_toSeq_2481_);
v___x_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2488_);
lean_ctor_set(v___x_2492_, 1, v___f_2484_);
lean_ctor_set(v___x_2492_, 2, v___f_2491_);
lean_ctor_set(v___x_2492_, 3, v___f_2490_);
lean_ctor_set(v___x_2492_, 4, v___f_2489_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___f_2485_);
v_cancelTk_x3f_2494_ = lean_ctor_get(v_a_2474_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2494_) == 1)
{
lean_object* v_val_2495_; uint8_t v___x_2496_; 
v_val_2495_ = lean_ctor_get(v_cancelTk_x3f_2494_, 0);
v___x_2496_ = l_IO_CancelToken_isSet(v_val_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec_ref_known(v___x_2493_, 2);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2497_ = lean_apply_5(v_inferType_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2189__overap_2503_; lean_object* v___x_2504_; 
v___x_2498_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2499_ = l_Lean_Core_instMonadRefCoreM;
v___x_2500_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2501_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2500_, v___x_2493_);
v___x_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2498_);
lean_ctor_set(v___x_2502_, 1, v___x_2499_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
v___x_2189__overap_2503_ = l_Lean_throwInterruptException___redArg(v___x_2502_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
v___x_2504_ = lean_apply_3(v___x_2189__overap_2503_, v_a_2474_, v_a_2475_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2505_; 
lean_dec_ref_known(v___x_2504_, 1);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2505_ = lean_apply_5(v_inferType_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
return v___x_2505_;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_inferType_2471_);
v_a_2506_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2504_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2504_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref_known(v___x_2493_, 2);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2514_ = lean_apply_5(v_inferType_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2627_, lean_object* v_inferType_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2627_, v_inferType_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___y_2642_; uint8_t v___y_2643_; uint8_t v___y_2644_; uint8_t v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2681_; lean_object* v___x_2739_; uint8_t v_transparency_2740_; uint8_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2739_ = l_Lean_Meta_Context_config(v_a_2636_);
v_transparency_2740_ = lean_ctor_get_uint8(v___x_2739_, 9);
lean_dec_ref(v___x_2739_);
v___x_2741_ = 1;
v___x_2742_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
v___y_2681_ = v_transparency_2740_;
goto v___jp_2680_;
}
else
{
v___y_2681_ = v___x_2741_;
goto v___jp_2680_;
}
v___jp_2641_:
{
lean_object* v___x_2653_; uint8_t v_foApprox_2654_; uint8_t v_ctxApprox_2655_; uint8_t v_quasiPatternApprox_2656_; uint8_t v_constApprox_2657_; uint8_t v_isDefEqStuckEx_2658_; uint8_t v_unificationHints_2659_; uint8_t v_proofIrrelevance_2660_; uint8_t v_assignSyntheticOpaque_2661_; uint8_t v_offsetCnstrs_2662_; uint8_t v_transparency_2663_; uint8_t v_univApprox_2664_; uint8_t v_zetaUnused_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2679_; 
v___x_2653_ = l_Lean_Meta_Context_config(v___y_2642_);
lean_dec_ref(v___y_2642_);
v_foApprox_2654_ = lean_ctor_get_uint8(v___x_2653_, 0);
v_ctxApprox_2655_ = lean_ctor_get_uint8(v___x_2653_, 1);
v_quasiPatternApprox_2656_ = lean_ctor_get_uint8(v___x_2653_, 2);
v_constApprox_2657_ = lean_ctor_get_uint8(v___x_2653_, 3);
v_isDefEqStuckEx_2658_ = lean_ctor_get_uint8(v___x_2653_, 4);
v_unificationHints_2659_ = lean_ctor_get_uint8(v___x_2653_, 5);
v_proofIrrelevance_2660_ = lean_ctor_get_uint8(v___x_2653_, 6);
v_assignSyntheticOpaque_2661_ = lean_ctor_get_uint8(v___x_2653_, 7);
v_offsetCnstrs_2662_ = lean_ctor_get_uint8(v___x_2653_, 8);
v_transparency_2663_ = lean_ctor_get_uint8(v___x_2653_, 9);
v_univApprox_2664_ = lean_ctor_get_uint8(v___x_2653_, 11);
v_zetaUnused_2665_ = lean_ctor_get_uint8(v___x_2653_, 17);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2667_ = v___x_2653_;
v_isShared_2668_ = v_isSharedCheck_2679_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2653_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2679_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; uint8_t v___x_2670_; uint8_t v___x_2671_; lean_object* v___x_2673_; 
v___x_2669_ = 1;
v___x_2670_ = 0;
v___x_2671_ = 2;
if (v_isShared_2668_ == 0)
{
v___x_2673_ = v___x_2667_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 0, v_foApprox_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 1, v_ctxApprox_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 2, v_quasiPatternApprox_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 3, v_constApprox_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 4, v_isDefEqStuckEx_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 5, v_unificationHints_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 6, v_proofIrrelevance_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 7, v_assignSyntheticOpaque_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 8, v_offsetCnstrs_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 9, v_transparency_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 11, v_univApprox_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2678_, 17, v_zetaUnused_2665_);
v___x_2673_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
uint64_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_ctor_set_uint8(v___x_2673_, 10, v___x_2670_);
lean_ctor_set_uint8(v___x_2673_, 12, v___x_2669_);
lean_ctor_set_uint8(v___x_2673_, 13, v___x_2669_);
lean_ctor_set_uint8(v___x_2673_, 14, v___x_2671_);
lean_ctor_set_uint8(v___x_2673_, 15, v___x_2669_);
lean_ctor_set_uint8(v___x_2673_, 16, v___x_2669_);
lean_ctor_set_uint8(v___x_2673_, 18, v___x_2669_);
v___x_2674_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set_uint64(v___x_2675_, sizeof(void*)*1, v___x_2674_);
lean_inc(v___y_2650_);
lean_inc(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2651_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2652_);
v___x_2676_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v___y_2652_);
lean_ctor_set(v___x_2676_, 2, v___y_2648_);
lean_ctor_set(v___x_2676_, 3, v___y_2651_);
lean_ctor_set(v___x_2676_, 4, v___y_2646_);
lean_ctor_set(v___x_2676_, 5, v___y_2647_);
lean_ctor_set(v___x_2676_, 6, v___y_2650_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*7, v___y_2645_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*7 + 1, v___y_2644_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*7 + 2, v___y_2643_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*7 + 3, v___y_2649_);
lean_inc(v_a_2639_);
lean_inc_ref(v_a_2638_);
lean_inc(v_a_2637_);
v___x_2677_ = lean_apply_5(v_x_2635_, v___x_2676_, v_a_2637_, v_a_2638_, v_a_2639_, lean_box(0));
return v___x_2677_;
}
}
}
v___jp_2680_:
{
lean_object* v___x_2682_; uint8_t v_foApprox_2683_; uint8_t v_ctxApprox_2684_; uint8_t v_quasiPatternApprox_2685_; uint8_t v_constApprox_2686_; uint8_t v_isDefEqStuckEx_2687_; uint8_t v_unificationHints_2688_; uint8_t v_proofIrrelevance_2689_; uint8_t v_assignSyntheticOpaque_2690_; uint8_t v_offsetCnstrs_2691_; uint8_t v_etaStruct_2692_; uint8_t v_univApprox_2693_; uint8_t v_iota_2694_; uint8_t v_beta_2695_; uint8_t v_proj_2696_; uint8_t v_zeta_2697_; uint8_t v_zetaDelta_2698_; uint8_t v_zetaUnused_2699_; uint8_t v_zetaHave_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2738_; 
v___x_2682_ = l_Lean_Meta_Context_config(v_a_2636_);
v_foApprox_2683_ = lean_ctor_get_uint8(v___x_2682_, 0);
v_ctxApprox_2684_ = lean_ctor_get_uint8(v___x_2682_, 1);
v_quasiPatternApprox_2685_ = lean_ctor_get_uint8(v___x_2682_, 2);
v_constApprox_2686_ = lean_ctor_get_uint8(v___x_2682_, 3);
v_isDefEqStuckEx_2687_ = lean_ctor_get_uint8(v___x_2682_, 4);
v_unificationHints_2688_ = lean_ctor_get_uint8(v___x_2682_, 5);
v_proofIrrelevance_2689_ = lean_ctor_get_uint8(v___x_2682_, 6);
v_assignSyntheticOpaque_2690_ = lean_ctor_get_uint8(v___x_2682_, 7);
v_offsetCnstrs_2691_ = lean_ctor_get_uint8(v___x_2682_, 8);
v_etaStruct_2692_ = lean_ctor_get_uint8(v___x_2682_, 10);
v_univApprox_2693_ = lean_ctor_get_uint8(v___x_2682_, 11);
v_iota_2694_ = lean_ctor_get_uint8(v___x_2682_, 12);
v_beta_2695_ = lean_ctor_get_uint8(v___x_2682_, 13);
v_proj_2696_ = lean_ctor_get_uint8(v___x_2682_, 14);
v_zeta_2697_ = lean_ctor_get_uint8(v___x_2682_, 15);
v_zetaDelta_2698_ = lean_ctor_get_uint8(v___x_2682_, 16);
v_zetaUnused_2699_ = lean_ctor_get_uint8(v___x_2682_, 17);
v_zetaHave_2700_ = lean_ctor_get_uint8(v___x_2682_, 18);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2702_ = v___x_2682_;
v_isShared_2703_ = v_isSharedCheck_2738_;
goto v_resetjp_2701_;
}
else
{
lean_dec(v___x_2682_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2738_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint8_t v_trackZetaDelta_2704_; lean_object* v_zetaDeltaSet_2705_; lean_object* v_lctx_2706_; lean_object* v_localInstances_2707_; lean_object* v_defEqCtx_x3f_2708_; lean_object* v_synthPendingDepth_2709_; lean_object* v_canUnfold_x3f_2710_; uint8_t v_univApprox_2711_; uint8_t v_inTypeClassResolution_2712_; uint8_t v_cacheInferType_2713_; lean_object* v_config_2715_; 
v_trackZetaDelta_2704_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*7);
v_zetaDeltaSet_2705_ = lean_ctor_get(v_a_2636_, 1);
v_lctx_2706_ = lean_ctor_get(v_a_2636_, 2);
v_localInstances_2707_ = lean_ctor_get(v_a_2636_, 3);
v_defEqCtx_x3f_2708_ = lean_ctor_get(v_a_2636_, 4);
v_synthPendingDepth_2709_ = lean_ctor_get(v_a_2636_, 5);
v_canUnfold_x3f_2710_ = lean_ctor_get(v_a_2636_, 6);
v_univApprox_2711_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2712_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*7 + 2);
v_cacheInferType_2713_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*7 + 3);
if (v_isShared_2703_ == 0)
{
v_config_2715_ = v___x_2702_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 0, v_foApprox_2683_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 1, v_ctxApprox_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 2, v_quasiPatternApprox_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 3, v_constApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 4, v_isDefEqStuckEx_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 5, v_unificationHints_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 6, v_proofIrrelevance_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 7, v_assignSyntheticOpaque_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 8, v_offsetCnstrs_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 10, v_etaStruct_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 11, v_univApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 12, v_iota_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 13, v_beta_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 14, v_proj_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 15, v_zeta_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 16, v_zetaDelta_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 17, v_zetaUnused_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2737_, 18, v_zetaHave_2700_);
v_config_2715_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
uint64_t v___x_2716_; uint64_t v___x_2717_; uint64_t v___x_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v_key_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v_beta_2725_; 
lean_ctor_set_uint8(v_config_2715_, 9, v___y_2681_);
v___x_2716_ = l_Lean_Meta_Context_configKey(v_a_2636_);
v___x_2717_ = 3ULL;
v___x_2718_ = lean_uint64_shift_right(v___x_2716_, v___x_2717_);
v___x_2719_ = lean_uint64_shift_left(v___x_2718_, v___x_2717_);
v___x_2720_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2681_);
v_key_2721_ = lean_uint64_lor(v___x_2719_, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2722_, 0, v_config_2715_);
lean_ctor_set_uint64(v___x_2722_, sizeof(void*)*1, v_key_2721_);
lean_inc(v_canUnfold_x3f_2710_);
lean_inc(v_synthPendingDepth_2709_);
lean_inc(v_defEqCtx_x3f_2708_);
lean_inc_ref(v_localInstances_2707_);
lean_inc_ref(v_lctx_2706_);
lean_inc(v_zetaDeltaSet_2705_);
v___x_2723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_zetaDeltaSet_2705_);
lean_ctor_set(v___x_2723_, 2, v_lctx_2706_);
lean_ctor_set(v___x_2723_, 3, v_localInstances_2707_);
lean_ctor_set(v___x_2723_, 4, v_defEqCtx_x3f_2708_);
lean_ctor_set(v___x_2723_, 5, v_synthPendingDepth_2709_);
lean_ctor_set(v___x_2723_, 6, v_canUnfold_x3f_2710_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7, v_trackZetaDelta_2704_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 1, v_univApprox_2711_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2712_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 3, v_cacheInferType_2713_);
v___x_2724_ = l_Lean_Meta_Context_config(v___x_2723_);
v_beta_2725_ = lean_ctor_get_uint8(v___x_2724_, 13);
if (v_beta_2725_ == 0)
{
lean_dec_ref(v___x_2724_);
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v_iota_2726_; 
v_iota_2726_ = lean_ctor_get_uint8(v___x_2724_, 12);
if (v_iota_2726_ == 0)
{
lean_dec_ref(v___x_2724_);
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v_zeta_2727_; 
v_zeta_2727_ = lean_ctor_get_uint8(v___x_2724_, 15);
if (v_zeta_2727_ == 0)
{
lean_dec_ref(v___x_2724_);
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v_zetaHave_2728_; 
v_zetaHave_2728_ = lean_ctor_get_uint8(v___x_2724_, 18);
if (v_zetaHave_2728_ == 0)
{
lean_dec_ref(v___x_2724_);
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v_zetaDelta_2729_; 
v_zetaDelta_2729_ = lean_ctor_get_uint8(v___x_2724_, 16);
if (v_zetaDelta_2729_ == 0)
{
lean_dec_ref(v___x_2724_);
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v_etaStruct_2730_; uint8_t v_proj_2731_; uint8_t v___x_2732_; uint8_t v___x_2733_; 
v_etaStruct_2730_ = lean_ctor_get_uint8(v___x_2724_, 10);
v_proj_2731_ = lean_ctor_get_uint8(v___x_2724_, 14);
lean_dec_ref(v___x_2724_);
v___x_2732_ = 2;
v___x_2733_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
uint8_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = 0;
v___x_2735_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2730_, v___x_2734_);
if (v___x_2735_ == 0)
{
v___y_2642_ = v___x_2723_;
v___y_2643_ = v_inTypeClassResolution_2712_;
v___y_2644_ = v_univApprox_2711_;
v___y_2645_ = v_trackZetaDelta_2704_;
v___y_2646_ = v_defEqCtx_x3f_2708_;
v___y_2647_ = v_synthPendingDepth_2709_;
v___y_2648_ = v_lctx_2706_;
v___y_2649_ = v_cacheInferType_2713_;
v___y_2650_ = v_canUnfold_x3f_2710_;
v___y_2651_ = v_localInstances_2707_;
v___y_2652_ = v_zetaDeltaSet_2705_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2736_; 
lean_inc(v_a_2639_);
lean_inc_ref(v_a_2638_);
lean_inc(v_a_2637_);
v___x_2736_ = lean_apply_5(v_x_2635_, v___x_2723_, v_a_2637_, v_a_2638_, v_a_2639_, lean_box(0));
return v___x_2736_;
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
lean_object* v___y_2758_; uint8_t v___y_2759_; uint8_t v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2797_; lean_object* v___x_2855_; uint8_t v_transparency_2856_; uint8_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = l_Lean_Meta_Context_config(v_a_2752_);
v_transparency_2856_ = lean_ctor_get_uint8(v___x_2855_, 9);
lean_dec_ref(v___x_2855_);
v___x_2857_ = 1;
v___x_2858_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
v___y_2797_ = v_transparency_2856_;
goto v___jp_2796_;
}
else
{
v___y_2797_ = v___x_2857_;
goto v___jp_2796_;
}
v___jp_2757_:
{
lean_object* v___x_2769_; uint8_t v_foApprox_2770_; uint8_t v_ctxApprox_2771_; uint8_t v_quasiPatternApprox_2772_; uint8_t v_constApprox_2773_; uint8_t v_isDefEqStuckEx_2774_; uint8_t v_unificationHints_2775_; uint8_t v_proofIrrelevance_2776_; uint8_t v_assignSyntheticOpaque_2777_; uint8_t v_offsetCnstrs_2778_; uint8_t v_transparency_2779_; uint8_t v_univApprox_2780_; uint8_t v_zetaUnused_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2795_; 
v___x_2769_ = l_Lean_Meta_Context_config(v___y_2758_);
lean_dec_ref(v___y_2758_);
v_foApprox_2770_ = lean_ctor_get_uint8(v___x_2769_, 0);
v_ctxApprox_2771_ = lean_ctor_get_uint8(v___x_2769_, 1);
v_quasiPatternApprox_2772_ = lean_ctor_get_uint8(v___x_2769_, 2);
v_constApprox_2773_ = lean_ctor_get_uint8(v___x_2769_, 3);
v_isDefEqStuckEx_2774_ = lean_ctor_get_uint8(v___x_2769_, 4);
v_unificationHints_2775_ = lean_ctor_get_uint8(v___x_2769_, 5);
v_proofIrrelevance_2776_ = lean_ctor_get_uint8(v___x_2769_, 6);
v_assignSyntheticOpaque_2777_ = lean_ctor_get_uint8(v___x_2769_, 7);
v_offsetCnstrs_2778_ = lean_ctor_get_uint8(v___x_2769_, 8);
v_transparency_2779_ = lean_ctor_get_uint8(v___x_2769_, 9);
v_univApprox_2780_ = lean_ctor_get_uint8(v___x_2769_, 11);
v_zetaUnused_2781_ = lean_ctor_get_uint8(v___x_2769_, 17);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2783_ = v___x_2769_;
v_isShared_2784_ = v_isSharedCheck_2795_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v___x_2769_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2795_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
uint8_t v___x_2785_; uint8_t v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2789_; 
v___x_2785_ = 1;
v___x_2786_ = 0;
v___x_2787_ = 2;
if (v_isShared_2784_ == 0)
{
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 0, v_foApprox_2770_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 1, v_ctxApprox_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 2, v_quasiPatternApprox_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 3, v_constApprox_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 4, v_isDefEqStuckEx_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 5, v_unificationHints_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 6, v_proofIrrelevance_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 7, v_assignSyntheticOpaque_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 8, v_offsetCnstrs_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 9, v_transparency_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 11, v_univApprox_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2794_, 17, v_zetaUnused_2781_);
v___x_2789_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
uint64_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_ctor_set_uint8(v___x_2789_, 10, v___x_2786_);
lean_ctor_set_uint8(v___x_2789_, 12, v___x_2785_);
lean_ctor_set_uint8(v___x_2789_, 13, v___x_2785_);
lean_ctor_set_uint8(v___x_2789_, 14, v___x_2787_);
lean_ctor_set_uint8(v___x_2789_, 15, v___x_2785_);
lean_ctor_set_uint8(v___x_2789_, 16, v___x_2785_);
lean_ctor_set_uint8(v___x_2789_, 18, v___x_2785_);
v___x_2790_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set_uint64(v___x_2791_, sizeof(void*)*1, v___x_2790_);
lean_inc(v___y_2766_);
lean_inc(v___y_2763_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2767_);
lean_inc_ref(v___y_2764_);
lean_inc(v___y_2768_);
v___x_2792_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___y_2768_);
lean_ctor_set(v___x_2792_, 2, v___y_2764_);
lean_ctor_set(v___x_2792_, 3, v___y_2767_);
lean_ctor_set(v___x_2792_, 4, v___y_2762_);
lean_ctor_set(v___x_2792_, 5, v___y_2763_);
lean_ctor_set(v___x_2792_, 6, v___y_2766_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7, v___y_2761_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 1, v___y_2760_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 2, v___y_2759_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*7 + 3, v___y_2765_);
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
v___x_2793_ = lean_apply_5(v_x_2751_, v___x_2792_, v_a_2753_, v_a_2754_, v_a_2755_, lean_box(0));
return v___x_2793_;
}
}
}
v___jp_2796_:
{
lean_object* v___x_2798_; uint8_t v_foApprox_2799_; uint8_t v_ctxApprox_2800_; uint8_t v_quasiPatternApprox_2801_; uint8_t v_constApprox_2802_; uint8_t v_isDefEqStuckEx_2803_; uint8_t v_unificationHints_2804_; uint8_t v_proofIrrelevance_2805_; uint8_t v_assignSyntheticOpaque_2806_; uint8_t v_offsetCnstrs_2807_; uint8_t v_etaStruct_2808_; uint8_t v_univApprox_2809_; uint8_t v_iota_2810_; uint8_t v_beta_2811_; uint8_t v_proj_2812_; uint8_t v_zeta_2813_; uint8_t v_zetaDelta_2814_; uint8_t v_zetaUnused_2815_; uint8_t v_zetaHave_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2854_; 
v___x_2798_ = l_Lean_Meta_Context_config(v_a_2752_);
v_foApprox_2799_ = lean_ctor_get_uint8(v___x_2798_, 0);
v_ctxApprox_2800_ = lean_ctor_get_uint8(v___x_2798_, 1);
v_quasiPatternApprox_2801_ = lean_ctor_get_uint8(v___x_2798_, 2);
v_constApprox_2802_ = lean_ctor_get_uint8(v___x_2798_, 3);
v_isDefEqStuckEx_2803_ = lean_ctor_get_uint8(v___x_2798_, 4);
v_unificationHints_2804_ = lean_ctor_get_uint8(v___x_2798_, 5);
v_proofIrrelevance_2805_ = lean_ctor_get_uint8(v___x_2798_, 6);
v_assignSyntheticOpaque_2806_ = lean_ctor_get_uint8(v___x_2798_, 7);
v_offsetCnstrs_2807_ = lean_ctor_get_uint8(v___x_2798_, 8);
v_etaStruct_2808_ = lean_ctor_get_uint8(v___x_2798_, 10);
v_univApprox_2809_ = lean_ctor_get_uint8(v___x_2798_, 11);
v_iota_2810_ = lean_ctor_get_uint8(v___x_2798_, 12);
v_beta_2811_ = lean_ctor_get_uint8(v___x_2798_, 13);
v_proj_2812_ = lean_ctor_get_uint8(v___x_2798_, 14);
v_zeta_2813_ = lean_ctor_get_uint8(v___x_2798_, 15);
v_zetaDelta_2814_ = lean_ctor_get_uint8(v___x_2798_, 16);
v_zetaUnused_2815_ = lean_ctor_get_uint8(v___x_2798_, 17);
v_zetaHave_2816_ = lean_ctor_get_uint8(v___x_2798_, 18);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2818_ = v___x_2798_;
v_isShared_2819_ = v_isSharedCheck_2854_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v___x_2798_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2854_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
uint8_t v_trackZetaDelta_2820_; lean_object* v_zetaDeltaSet_2821_; lean_object* v_lctx_2822_; lean_object* v_localInstances_2823_; lean_object* v_defEqCtx_x3f_2824_; lean_object* v_synthPendingDepth_2825_; lean_object* v_canUnfold_x3f_2826_; uint8_t v_univApprox_2827_; uint8_t v_inTypeClassResolution_2828_; uint8_t v_cacheInferType_2829_; lean_object* v_config_2831_; 
v_trackZetaDelta_2820_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7);
v_zetaDeltaSet_2821_ = lean_ctor_get(v_a_2752_, 1);
v_lctx_2822_ = lean_ctor_get(v_a_2752_, 2);
v_localInstances_2823_ = lean_ctor_get(v_a_2752_, 3);
v_defEqCtx_x3f_2824_ = lean_ctor_get(v_a_2752_, 4);
v_synthPendingDepth_2825_ = lean_ctor_get(v_a_2752_, 5);
v_canUnfold_x3f_2826_ = lean_ctor_get(v_a_2752_, 6);
v_univApprox_2827_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2828_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 2);
v_cacheInferType_2829_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*7 + 3);
if (v_isShared_2819_ == 0)
{
v_config_2831_ = v___x_2818_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 0, v_foApprox_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 1, v_ctxApprox_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 2, v_quasiPatternApprox_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 3, v_constApprox_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 4, v_isDefEqStuckEx_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 5, v_unificationHints_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 6, v_proofIrrelevance_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 7, v_assignSyntheticOpaque_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 8, v_offsetCnstrs_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 10, v_etaStruct_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 11, v_univApprox_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 12, v_iota_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 13, v_beta_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 14, v_proj_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 15, v_zeta_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 16, v_zetaDelta_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 17, v_zetaUnused_2815_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, 18, v_zetaHave_2816_);
v_config_2831_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
uint64_t v___x_2832_; uint64_t v___x_2833_; uint64_t v___x_2834_; uint64_t v___x_2835_; uint64_t v___x_2836_; uint64_t v_key_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v_beta_2841_; 
lean_ctor_set_uint8(v_config_2831_, 9, v___y_2797_);
v___x_2832_ = l_Lean_Meta_Context_configKey(v_a_2752_);
v___x_2833_ = 3ULL;
v___x_2834_ = lean_uint64_shift_right(v___x_2832_, v___x_2833_);
v___x_2835_ = lean_uint64_shift_left(v___x_2834_, v___x_2833_);
v___x_2836_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2797_);
v_key_2837_ = lean_uint64_lor(v___x_2835_, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2838_, 0, v_config_2831_);
lean_ctor_set_uint64(v___x_2838_, sizeof(void*)*1, v_key_2837_);
lean_inc(v_canUnfold_x3f_2826_);
lean_inc(v_synthPendingDepth_2825_);
lean_inc(v_defEqCtx_x3f_2824_);
lean_inc_ref(v_localInstances_2823_);
lean_inc_ref(v_lctx_2822_);
lean_inc(v_zetaDeltaSet_2821_);
v___x_2839_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v_zetaDeltaSet_2821_);
lean_ctor_set(v___x_2839_, 2, v_lctx_2822_);
lean_ctor_set(v___x_2839_, 3, v_localInstances_2823_);
lean_ctor_set(v___x_2839_, 4, v_defEqCtx_x3f_2824_);
lean_ctor_set(v___x_2839_, 5, v_synthPendingDepth_2825_);
lean_ctor_set(v___x_2839_, 6, v_canUnfold_x3f_2826_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*7, v_trackZetaDelta_2820_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*7 + 1, v_univApprox_2827_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2828_);
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*7 + 3, v_cacheInferType_2829_);
v___x_2840_ = l_Lean_Meta_Context_config(v___x_2839_);
v_beta_2841_ = lean_ctor_get_uint8(v___x_2840_, 13);
if (v_beta_2841_ == 0)
{
lean_dec_ref(v___x_2840_);
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v_iota_2842_; 
v_iota_2842_ = lean_ctor_get_uint8(v___x_2840_, 12);
if (v_iota_2842_ == 0)
{
lean_dec_ref(v___x_2840_);
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v_zeta_2843_; 
v_zeta_2843_ = lean_ctor_get_uint8(v___x_2840_, 15);
if (v_zeta_2843_ == 0)
{
lean_dec_ref(v___x_2840_);
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v_zetaHave_2844_; 
v_zetaHave_2844_ = lean_ctor_get_uint8(v___x_2840_, 18);
if (v_zetaHave_2844_ == 0)
{
lean_dec_ref(v___x_2840_);
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v_zetaDelta_2845_; 
v_zetaDelta_2845_ = lean_ctor_get_uint8(v___x_2840_, 16);
if (v_zetaDelta_2845_ == 0)
{
lean_dec_ref(v___x_2840_);
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v_etaStruct_2846_; uint8_t v_proj_2847_; uint8_t v___x_2848_; uint8_t v___x_2849_; 
v_etaStruct_2846_ = lean_ctor_get_uint8(v___x_2840_, 10);
v_proj_2847_ = lean_ctor_get_uint8(v___x_2840_, 14);
lean_dec_ref(v___x_2840_);
v___x_2848_ = 2;
v___x_2849_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
uint8_t v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = 0;
v___x_2851_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2846_, v___x_2850_);
if (v___x_2851_ == 0)
{
v___y_2758_ = v___x_2839_;
v___y_2759_ = v_inTypeClassResolution_2828_;
v___y_2760_ = v_univApprox_2827_;
v___y_2761_ = v_trackZetaDelta_2820_;
v___y_2762_ = v_defEqCtx_x3f_2824_;
v___y_2763_ = v_synthPendingDepth_2825_;
v___y_2764_ = v_lctx_2822_;
v___y_2765_ = v_cacheInferType_2829_;
v___y_2766_ = v_canUnfold_x3f_2826_;
v___y_2767_ = v_localInstances_2823_;
v___y_2768_ = v_zetaDeltaSet_2821_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2852_; 
lean_inc(v_a_2755_);
lean_inc_ref(v_a_2754_);
lean_inc(v_a_2753_);
v___x_2852_ = lean_apply_5(v_x_2751_, v___x_2839_, v_a_2753_, v_a_2754_, v_a_2755_, lean_box(0));
return v___x_2852_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2859_, lean_object* v_x_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2859_, v_x_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
return v_res_2866_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = l_Lean_interruptExceptionId;
v___x_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
lean_object* v_ks_2889_; lean_object* v_vs_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2919_; 
v_ks_2889_ = lean_ctor_get(v_x_2885_, 0);
v_vs_2890_ = lean_ctor_get(v_x_2885_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_x_2885_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2892_ = v_x_2885_;
v_isShared_2893_ = v_isSharedCheck_2919_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_vs_2890_);
lean_inc(v_ks_2889_);
lean_dec(v_x_2885_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2919_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
uint8_t v___y_2895_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = lean_array_get_size(v_ks_2889_);
v___x_2908_ = lean_nat_dec_lt(v_x_2886_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_del_object(v___x_2892_);
lean_dec(v_x_2886_);
v___x_2909_ = lean_array_push(v_ks_2889_, v_x_2887_);
v___x_2910_ = lean_array_push(v_vs_2890_, v_x_2888_);
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
return v___x_2911_;
}
else
{
lean_object* v_expr_2912_; uint64_t v_configKey_2913_; lean_object* v_k_x27_2914_; lean_object* v_expr_2915_; uint64_t v_configKey_2916_; uint8_t v___x_2917_; 
v_expr_2912_ = lean_ctor_get(v_x_2887_, 0);
v_configKey_2913_ = lean_ctor_get_uint64(v_x_2887_, sizeof(void*)*1);
v_k_x27_2914_ = lean_array_fget_borrowed(v_ks_2889_, v_x_2886_);
v_expr_2915_ = lean_ctor_get(v_k_x27_2914_, 0);
v_configKey_2916_ = lean_ctor_get_uint64(v_k_x27_2914_, sizeof(void*)*1);
v___x_2917_ = lean_expr_equal(v_expr_2912_, v_expr_2915_);
if (v___x_2917_ == 0)
{
v___y_2895_ = v___x_2917_;
goto v___jp_2894_;
}
else
{
uint8_t v___x_2918_; 
v___x_2918_ = lean_uint64_dec_eq(v_configKey_2913_, v_configKey_2916_);
v___y_2895_ = v___x_2918_;
goto v___jp_2894_;
}
}
v___jp_2894_:
{
if (v___y_2895_ == 0)
{
lean_object* v___x_2897_; 
if (v_isShared_2893_ == 0)
{
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_ks_2889_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_vs_2890_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_unsigned_to_nat(1u);
v___x_2899_ = lean_nat_add(v_x_2886_, v___x_2898_);
lean_dec(v_x_2886_);
v_x_2885_ = v___x_2897_;
v_x_2886_ = v___x_2899_;
goto _start;
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2902_ = lean_array_fset(v_ks_2889_, v_x_2886_, v_x_2887_);
v___x_2903_ = lean_array_fset(v_vs_2890_, v_x_2886_, v_x_2888_);
lean_dec(v_x_2886_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v___x_2903_);
lean_ctor_set(v___x_2892_, 0, v___x_2902_);
v___x_2905_ = v___x_2892_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2920_, lean_object* v_k_2921_, lean_object* v_v_2922_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2920_, v___x_2923_, v_k_2921_, v_v_2922_);
return v___x_2924_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2926_, size_t v_x_2927_, size_t v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
if (lean_obj_tag(v_x_2926_) == 0)
{
lean_object* v_es_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; lean_object* v_j_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_es_2931_ = lean_ctor_get(v_x_2926_, 0);
v___x_2932_ = ((size_t)5ULL);
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2935_ = lean_usize_land(v_x_2927_, v___x_2934_);
v_j_2936_ = lean_usize_to_nat(v___x_2935_);
v___x_2937_ = lean_array_get_size(v_es_2931_);
v___x_2938_ = lean_nat_dec_lt(v_j_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_dec(v_j_2936_);
lean_dec(v_x_2930_);
lean_dec_ref(v_x_2929_);
return v_x_2926_;
}
else
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2982_; 
lean_inc_ref(v_es_2931_);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_x_2926_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_x_2926_, 0);
lean_dec(v_unused_2983_);
v___x_2940_ = v_x_2926_;
v_isShared_2941_ = v_isSharedCheck_2982_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v_x_2926_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2982_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_v_2942_; lean_object* v___x_2943_; lean_object* v_xs_x27_2944_; lean_object* v___y_2946_; 
v_v_2942_ = lean_array_fget(v_es_2931_, v_j_2936_);
v___x_2943_ = lean_box(0);
v_xs_x27_2944_ = lean_array_fset(v_es_2931_, v_j_2936_, v___x_2943_);
switch(lean_obj_tag(v_v_2942_))
{
case 0:
{
lean_object* v_key_2951_; lean_object* v_val_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2969_; 
v_key_2951_ = lean_ctor_get(v_v_2942_, 0);
v_val_2952_ = lean_ctor_get(v_v_2942_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_v_2942_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2954_ = v_v_2942_;
v_isShared_2955_ = v_isSharedCheck_2969_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_val_2952_);
lean_inc(v_key_2951_);
lean_dec(v_v_2942_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2969_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
uint8_t v___y_2957_; lean_object* v_expr_2963_; uint64_t v_configKey_2964_; lean_object* v_expr_2965_; uint64_t v_configKey_2966_; uint8_t v___x_2967_; 
v_expr_2963_ = lean_ctor_get(v_x_2929_, 0);
v_configKey_2964_ = lean_ctor_get_uint64(v_x_2929_, sizeof(void*)*1);
v_expr_2965_ = lean_ctor_get(v_key_2951_, 0);
v_configKey_2966_ = lean_ctor_get_uint64(v_key_2951_, sizeof(void*)*1);
v___x_2967_ = lean_expr_equal(v_expr_2963_, v_expr_2965_);
if (v___x_2967_ == 0)
{
v___y_2957_ = v___x_2967_;
goto v___jp_2956_;
}
else
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_uint64_dec_eq(v_configKey_2964_, v_configKey_2966_);
v___y_2957_ = v___x_2968_;
goto v___jp_2956_;
}
v___jp_2956_:
{
if (v___y_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_del_object(v___x_2954_);
v___x_2958_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2951_, v_val_2952_, v_x_2929_, v_x_2930_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
v___y_2946_ = v___x_2959_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2961_; 
lean_dec(v_val_2952_);
lean_dec(v_key_2951_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v_x_2930_);
lean_ctor_set(v___x_2954_, 0, v_x_2929_);
v___x_2961_ = v___x_2954_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_x_2929_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_x_2930_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
v___y_2946_ = v___x_2961_;
goto v___jp_2945_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2980_; 
v_node_2970_ = lean_ctor_get(v_v_2942_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_v_2942_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2972_ = v_v_2942_;
v_isShared_2973_ = v_isSharedCheck_2980_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_node_2970_);
lean_dec(v_v_2942_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2980_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2974_ = lean_usize_shift_right(v_x_2927_, v___x_2932_);
v___x_2975_ = lean_usize_add(v_x_2928_, v___x_2933_);
v___x_2976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2970_, v___x_2974_, v___x_2975_, v_x_2929_, v_x_2930_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2976_);
v___x_2978_ = v___x_2972_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
v___y_2946_ = v___x_2978_;
goto v___jp_2945_;
}
}
}
default: 
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_x_2929_);
lean_ctor_set(v___x_2981_, 1, v_x_2930_);
v___y_2946_ = v___x_2981_;
goto v___jp_2945_;
}
}
v___jp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = lean_array_fset(v_xs_x27_2944_, v_j_2936_, v___y_2946_);
lean_dec(v_j_2936_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2947_);
v___x_2949_ = v___x_2940_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
else
{
lean_object* v_ks_2984_; lean_object* v_vs_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3005_; 
v_ks_2984_ = lean_ctor_get(v_x_2926_, 0);
v_vs_2985_ = lean_ctor_get(v_x_2926_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_x_2926_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2987_ = v_x_2926_;
v_isShared_2988_ = v_isSharedCheck_3005_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_vs_2985_);
lean_inc(v_ks_2984_);
lean_dec(v_x_2926_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3005_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_ks_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_vs_2985_);
v___x_2990_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v_newNode_2991_; uint8_t v___y_2993_; size_t v___x_2999_; uint8_t v___x_3000_; 
v_newNode_2991_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2990_, v_x_2929_, v_x_2930_);
v___x_2999_ = ((size_t)7ULL);
v___x_3000_ = lean_usize_dec_le(v___x_2999_, v_x_2928_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3001_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2991_);
v___x_3002_ = lean_unsigned_to_nat(4u);
v___x_3003_ = lean_nat_dec_lt(v___x_3001_, v___x_3002_);
lean_dec(v___x_3001_);
v___y_2993_ = v___x_3003_;
goto v___jp_2992_;
}
else
{
v___y_2993_ = v___x_3000_;
goto v___jp_2992_;
}
v___jp_2992_:
{
if (v___y_2993_ == 0)
{
lean_object* v_ks_2994_; lean_object* v_vs_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_ks_2994_ = lean_ctor_get(v_newNode_2991_, 0);
lean_inc_ref(v_ks_2994_);
v_vs_2995_ = lean_ctor_get(v_newNode_2991_, 1);
lean_inc_ref(v_vs_2995_);
lean_dec_ref(v_newNode_2991_);
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2998_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2928_, v_ks_2994_, v_vs_2995_, v___x_2996_, v___x_2997_);
lean_dec_ref(v_vs_2995_);
lean_dec_ref(v_ks_2994_);
return v___x_2998_;
}
else
{
return v_newNode_2991_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3006_, lean_object* v_keys_3007_, lean_object* v_vals_3008_, lean_object* v_i_3009_, lean_object* v_entries_3010_){
_start:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = lean_array_get_size(v_keys_3007_);
v___x_3012_ = lean_nat_dec_lt(v_i_3009_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_dec(v_i_3009_);
return v_entries_3010_;
}
else
{
lean_object* v_k_3013_; lean_object* v_expr_3014_; uint64_t v_configKey_3015_; lean_object* v_v_3016_; uint64_t v___x_3017_; uint64_t v___x_3018_; size_t v_h_3019_; size_t v___x_3020_; lean_object* v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; size_t v___x_3024_; size_t v_h_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_k_3013_ = lean_array_fget_borrowed(v_keys_3007_, v_i_3009_);
v_expr_3014_ = lean_ctor_get(v_k_3013_, 0);
v_configKey_3015_ = lean_ctor_get_uint64(v_k_3013_, sizeof(void*)*1);
v_v_3016_ = lean_array_fget_borrowed(v_vals_3008_, v_i_3009_);
v___x_3017_ = l_Lean_Expr_hash(v_expr_3014_);
v___x_3018_ = lean_uint64_mix_hash(v___x_3017_, v_configKey_3015_);
v_h_3019_ = lean_uint64_to_usize(v___x_3018_);
v___x_3020_ = ((size_t)5ULL);
v___x_3021_ = lean_unsigned_to_nat(1u);
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_sub(v_depth_3006_, v___x_3022_);
v___x_3024_ = lean_usize_mul(v___x_3020_, v___x_3023_);
v_h_3025_ = lean_usize_shift_right(v_h_3019_, v___x_3024_);
v___x_3026_ = lean_nat_add(v_i_3009_, v___x_3021_);
lean_dec(v_i_3009_);
lean_inc(v_v_3016_);
lean_inc(v_k_3013_);
v___x_3027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3010_, v_h_3025_, v_depth_3006_, v_k_3013_, v_v_3016_);
v_i_3009_ = v___x_3026_;
v_entries_3010_ = v___x_3027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3029_, lean_object* v_keys_3030_, lean_object* v_vals_3031_, lean_object* v_i_3032_, lean_object* v_entries_3033_){
_start:
{
size_t v_depth_boxed_3034_; lean_object* v_res_3035_; 
v_depth_boxed_3034_ = lean_unbox_usize(v_depth_3029_);
lean_dec(v_depth_3029_);
v_res_3035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3034_, v_keys_3030_, v_vals_3031_, v_i_3032_, v_entries_3033_);
lean_dec_ref(v_vals_3031_);
lean_dec_ref(v_keys_3030_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
size_t v_x_2774__boxed_3041_; size_t v_x_2775__boxed_3042_; lean_object* v_res_3043_; 
v_x_2774__boxed_3041_ = lean_unbox_usize(v_x_3037_);
lean_dec(v_x_3037_);
v_x_2775__boxed_3042_ = lean_unbox_usize(v_x_3038_);
lean_dec(v_x_3038_);
v_res_3043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3036_, v_x_2774__boxed_3041_, v_x_2775__boxed_3042_, v_x_3039_, v_x_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_){
_start:
{
lean_object* v_expr_3047_; uint64_t v_configKey_3048_; uint64_t v___x_3049_; uint64_t v___x_3050_; size_t v___x_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v_expr_3047_ = lean_ctor_get(v_x_3045_, 0);
v_configKey_3048_ = lean_ctor_get_uint64(v_x_3045_, sizeof(void*)*1);
v___x_3049_ = l_Lean_Expr_hash(v_expr_3047_);
v___x_3050_ = lean_uint64_mix_hash(v___x_3049_, v_configKey_3048_);
v___x_3051_ = lean_uint64_to_usize(v___x_3050_);
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3044_, v___x_3051_, v___x_3052_, v_x_3045_, v_x_3046_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3054_, lean_object* v_vals_3055_, lean_object* v_i_3056_, lean_object* v_k_3057_){
_start:
{
uint8_t v___y_3059_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3065_ = lean_array_get_size(v_keys_3054_);
v___x_3066_ = lean_nat_dec_lt(v_i_3056_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
lean_dec(v_i_3056_);
v___x_3067_ = lean_box(0);
return v___x_3067_;
}
else
{
lean_object* v_expr_3068_; uint64_t v_configKey_3069_; lean_object* v_k_x27_3070_; lean_object* v_expr_3071_; uint64_t v_configKey_3072_; uint8_t v___x_3073_; 
v_expr_3068_ = lean_ctor_get(v_k_3057_, 0);
v_configKey_3069_ = lean_ctor_get_uint64(v_k_3057_, sizeof(void*)*1);
v_k_x27_3070_ = lean_array_fget_borrowed(v_keys_3054_, v_i_3056_);
v_expr_3071_ = lean_ctor_get(v_k_x27_3070_, 0);
v_configKey_3072_ = lean_ctor_get_uint64(v_k_x27_3070_, sizeof(void*)*1);
v___x_3073_ = lean_expr_equal(v_expr_3068_, v_expr_3071_);
if (v___x_3073_ == 0)
{
v___y_3059_ = v___x_3073_;
goto v___jp_3058_;
}
else
{
uint8_t v___x_3074_; 
v___x_3074_ = lean_uint64_dec_eq(v_configKey_3069_, v_configKey_3072_);
v___y_3059_ = v___x_3074_;
goto v___jp_3058_;
}
}
v___jp_3058_:
{
if (v___y_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_add(v_i_3056_, v___x_3060_);
lean_dec(v_i_3056_);
v_i_3056_ = v___x_3061_;
goto _start;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_array_fget_borrowed(v_vals_3055_, v_i_3056_);
lean_dec(v_i_3056_);
lean_inc(v___x_3063_);
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3075_, lean_object* v_vals_3076_, lean_object* v_i_3077_, lean_object* v_k_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3075_, v_vals_3076_, v_i_3077_, v_k_3078_);
lean_dec_ref(v_k_3078_);
lean_dec_ref(v_vals_3076_);
lean_dec_ref(v_keys_3075_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3080_, size_t v_x_3081_, lean_object* v_x_3082_){
_start:
{
if (lean_obj_tag(v_x_3080_) == 0)
{
lean_object* v_es_3083_; lean_object* v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; lean_object* v_j_3088_; lean_object* v___x_3089_; 
v_es_3083_ = lean_ctor_get(v_x_3080_, 0);
v___x_3084_ = lean_box(2);
v___x_3085_ = ((size_t)5ULL);
v___x_3086_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3087_ = lean_usize_land(v_x_3081_, v___x_3086_);
v_j_3088_ = lean_usize_to_nat(v___x_3087_);
v___x_3089_ = lean_array_get_borrowed(v___x_3084_, v_es_3083_, v_j_3088_);
lean_dec(v_j_3088_);
switch(lean_obj_tag(v___x_3089_))
{
case 0:
{
lean_object* v_key_3090_; lean_object* v_val_3091_; uint8_t v___y_3093_; lean_object* v_expr_3096_; uint64_t v_configKey_3097_; lean_object* v_expr_3098_; uint64_t v_configKey_3099_; uint8_t v___x_3100_; 
v_key_3090_ = lean_ctor_get(v___x_3089_, 0);
v_val_3091_ = lean_ctor_get(v___x_3089_, 1);
v_expr_3096_ = lean_ctor_get(v_x_3082_, 0);
v_configKey_3097_ = lean_ctor_get_uint64(v_x_3082_, sizeof(void*)*1);
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
lean_object* v_node_3102_; size_t v___x_3103_; 
v_node_3102_ = lean_ctor_get(v___x_3089_, 0);
v___x_3103_ = lean_usize_shift_right(v_x_3081_, v___x_3085_);
v_x_3080_ = v_node_3102_;
v_x_3081_ = v___x_3103_;
goto _start;
}
default: 
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_box(0);
return v___x_3105_;
}
}
}
else
{
lean_object* v_ks_3106_; lean_object* v_vs_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_ks_3106_ = lean_ctor_get(v_x_3080_, 0);
v_vs_3107_ = lean_ctor_get(v_x_3080_, 1);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3106_, v_vs_3107_, v___x_3108_, v_x_3082_);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
size_t v_x_2989__boxed_3113_; lean_object* v_res_3114_; 
v_x_2989__boxed_3113_ = lean_unbox_usize(v_x_3111_);
lean_dec(v_x_3111_);
v_res_3114_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3110_, v_x_2989__boxed_3113_, v_x_3112_);
lean_dec_ref(v_x_3112_);
lean_dec_ref(v_x_3110_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
lean_object* v_expr_3117_; uint64_t v_configKey_3118_; uint64_t v___x_3119_; uint64_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; 
v_expr_3117_ = lean_ctor_get(v_x_3116_, 0);
v_configKey_3118_ = lean_ctor_get_uint64(v_x_3116_, sizeof(void*)*1);
v___x_3119_ = l_Lean_Expr_hash(v_expr_3117_);
v___x_3120_ = lean_uint64_mix_hash(v___x_3119_, v_configKey_3118_);
v___x_3121_ = lean_uint64_to_usize(v___x_3120_);
v___x_3122_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3115_, v___x_3121_, v_x_3116_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3123_, v_x_3124_);
lean_dec_ref(v_x_3124_);
lean_dec_ref(v_x_3123_);
return v_res_3125_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3128_ = l_Lean_stringToMessageData(v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
switch(lean_obj_tag(v_e_3129_))
{
case 0:
{
lean_object* v_deBruijnIndex_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_deBruijnIndex_3165_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_deBruijnIndex_3165_);
lean_dec_ref_known(v_e_3129_, 1);
v___x_3166_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3167_ = l_Lean_mkBVar(v_deBruijnIndex_3165_);
v___x_3168_ = l_Lean_MessageData_ofExpr(v___x_3167_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3169_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3170_;
}
case 1:
{
lean_object* v_fvarId_3171_; lean_object* v___x_3172_; 
v_fvarId_3171_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_fvarId_3171_);
lean_dec_ref_known(v_e_3129_, 1);
v___x_3172_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3171_, v_a_3130_, v_a_3132_, v_a_3133_);
return v___x_3172_;
}
case 2:
{
lean_object* v_mvarId_3173_; lean_object* v___x_3174_; 
v_mvarId_3173_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_mvarId_3173_);
lean_dec_ref_known(v_e_3129_, 1);
v___x_3174_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3173_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3174_;
}
case 3:
{
lean_object* v_u_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_u_3175_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_u_3175_);
lean_dec_ref_known(v_e_3129_, 1);
v___x_3176_ = l_Lean_Level_succ___override(v_u_3175_);
v___x_3177_ = l_Lean_mkSort(v___x_3176_);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
case 4:
{
lean_object* v_declName_3179_; lean_object* v_us_3180_; 
v_declName_3179_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_declName_3179_);
v_us_3180_ = lean_ctor_get(v_e_3129_, 1);
lean_inc(v_us_3180_);
if (lean_obj_tag(v_us_3180_) == 0)
{
lean_object* v___x_3196_; 
lean_dec_ref_known(v_e_3129_, 2);
v___x_3196_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3179_, v_us_3180_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3196_;
}
else
{
uint8_t v_cacheInferType_3197_; 
v_cacheInferType_3197_ = lean_ctor_get_uint8(v_a_3130_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3197_ == 0)
{
lean_dec_ref_known(v_e_3129_, 2);
goto v___jp_3181_;
}
else
{
uint8_t v___x_3198_; 
v___x_3198_ = l_Lean_Expr_hasMVar(v_e_3129_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3264_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3264_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3264_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3244_; lean_object* v_cache_3245_; lean_object* v_inferType_3246_; lean_object* v___x_3247_; 
v___x_3244_ = lean_st_ref_get(v_a_3131_);
v_cache_3245_ = lean_ctor_get(v___x_3244_, 1);
lean_inc_ref(v_cache_3245_);
lean_dec(v___x_3244_);
v_inferType_3246_ = lean_ctor_get(v_cache_3245_, 0);
lean_inc_ref(v_inferType_3246_);
lean_dec_ref(v_cache_3245_);
v___x_3247_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3246_, v_a_3200_);
lean_dec_ref(v_inferType_3246_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_cancelTk_x3f_3248_; 
lean_del_object(v___x_3202_);
v_cancelTk_x3f_3248_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3248_) == 1)
{
lean_object* v_val_3249_; uint8_t v___x_3250_; 
v_val_3249_ = lean_ctor_get(v_cancelTk_x3f_3248_, 0);
v___x_3250_ = l_IO_CancelToken_isSet(v_val_3249_);
if (v___x_3250_ == 0)
{
goto v___jp_3204_;
}
else
{
lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_a_3200_);
lean_dec(v_us_3180_);
lean_dec(v_declName_3179_);
v___x_3251_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
goto v___jp_3204_;
}
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; 
lean_dec(v_a_3200_);
lean_dec(v_us_3180_);
lean_dec(v_declName_3179_);
v_val_3260_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_val_3260_);
lean_dec_ref_known(v___x_3247_, 1);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v_val_3260_);
v___x_3262_ = v___x_3202_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_val_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
v___jp_3204_:
{
lean_object* v___x_3205_; 
v___x_3205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3179_, v_us_3180_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; uint8_t v___x_3207_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
v___x_3207_ = l_Lean_Expr_hasMVar(v_a_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3242_; 
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3243_);
v___x_3209_ = v___x_3205_;
v_isShared_3210_ = v_isSharedCheck_3242_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v___x_3205_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3242_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v_cache_3212_; lean_object* v_mctx_3213_; lean_object* v_zetaDeltaFVarIds_3214_; lean_object* v_postponed_3215_; lean_object* v_diag_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3241_; 
v___x_3211_ = lean_st_ref_take(v_a_3131_);
v_cache_3212_ = lean_ctor_get(v___x_3211_, 1);
v_mctx_3213_ = lean_ctor_get(v___x_3211_, 0);
v_zetaDeltaFVarIds_3214_ = lean_ctor_get(v___x_3211_, 2);
v_postponed_3215_ = lean_ctor_get(v___x_3211_, 3);
v_diag_3216_ = lean_ctor_get(v___x_3211_, 4);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3218_ = v___x_3211_;
v_isShared_3219_ = v_isSharedCheck_3241_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_diag_3216_);
lean_inc(v_postponed_3215_);
lean_inc(v_zetaDeltaFVarIds_3214_);
lean_inc(v_cache_3212_);
lean_inc(v_mctx_3213_);
lean_dec(v___x_3211_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3241_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v_inferType_3220_; lean_object* v_funInfo_3221_; lean_object* v_synthInstance_3222_; lean_object* v_whnf_3223_; lean_object* v_defEqTrans_3224_; lean_object* v_defEqPerm_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3240_; 
v_inferType_3220_ = lean_ctor_get(v_cache_3212_, 0);
v_funInfo_3221_ = lean_ctor_get(v_cache_3212_, 1);
v_synthInstance_3222_ = lean_ctor_get(v_cache_3212_, 2);
v_whnf_3223_ = lean_ctor_get(v_cache_3212_, 3);
v_defEqTrans_3224_ = lean_ctor_get(v_cache_3212_, 4);
v_defEqPerm_3225_ = lean_ctor_get(v_cache_3212_, 5);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_cache_3212_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3227_ = v_cache_3212_;
v_isShared_3228_ = v_isSharedCheck_3240_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_defEqPerm_3225_);
lean_inc(v_defEqTrans_3224_);
lean_inc(v_whnf_3223_);
lean_inc(v_synthInstance_3222_);
lean_inc(v_funInfo_3221_);
lean_inc(v_inferType_3220_);
lean_dec(v_cache_3212_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3240_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_inc(v_a_3206_);
v___x_3229_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3220_, v_a_3200_, v_a_3206_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_funInfo_3221_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_synthInstance_3222_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_whnf_3223_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_defEqTrans_3224_);
lean_ctor_set(v_reuseFailAlloc_3239_, 5, v_defEqPerm_3225_);
v___x_3231_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3231_);
v___x_3233_ = v___x_3218_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_mctx_3213_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_zetaDeltaFVarIds_3214_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_postponed_3215_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_diag_3216_);
v___x_3233_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_st_ref_set(v_a_3131_, v___x_3233_);
if (v_isShared_3210_ == 0)
{
v___x_3236_ = v___x_3209_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3206_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3206_);
lean_dec(v_a_3200_);
return v___x_3205_;
}
}
else
{
lean_dec(v_a_3200_);
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec(v_us_3180_);
lean_dec(v_declName_3179_);
v_a_3265_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3199_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3199_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3129_, 2);
goto v___jp_3181_;
}
}
}
v___jp_3181_:
{
lean_object* v_cancelTk_x3f_3182_; 
v_cancelTk_x3f_3182_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3182_) == 1)
{
lean_object* v_val_3183_; uint8_t v___x_3184_; 
v_val_3183_ = lean_ctor_get(v_cancelTk_x3f_3182_, 0);
v___x_3184_ = l_IO_CancelToken_isSet(v_val_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3179_, v_us_3180_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_us_3180_);
lean_dec(v_declName_3179_);
v___x_3186_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3179_, v_us_3180_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3195_;
}
}
}
case 5:
{
lean_object* v_fn_3273_; uint8_t v_cacheInferType_3274_; lean_object* v_nargs_3275_; lean_object* v___x_3276_; lean_object* v_dummy_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_fn_3273_ = lean_ctor_get(v_e_3129_, 0);
v_cacheInferType_3274_ = lean_ctor_get_uint8(v_a_3130_, sizeof(void*)*7 + 3);
v_nargs_3275_ = l_Lean_Expr_getAppNumArgs(v_e_3129_);
v___x_3276_ = l_Lean_Expr_getAppFn(v_fn_3273_);
v_dummy_3277_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3275_);
v___x_3278_ = lean_mk_array(v_nargs_3275_, v_dummy_3277_);
v___x_3279_ = lean_unsigned_to_nat(1u);
v___x_3280_ = lean_nat_sub(v_nargs_3275_, v___x_3279_);
lean_dec(v_nargs_3275_);
lean_inc_ref(v_e_3129_);
v___x_3281_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3129_, v___x_3278_, v___x_3280_);
if (v_cacheInferType_3274_ == 0)
{
lean_dec_ref_known(v_e_3129_, 2);
goto v___jp_3282_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = l_Lean_Expr_hasMVar(v_e_3129_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3363_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3363_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3363_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3343_; lean_object* v_cache_3344_; lean_object* v_inferType_3345_; lean_object* v___x_3346_; 
v___x_3343_ = lean_st_ref_get(v_a_3131_);
v_cache_3344_ = lean_ctor_get(v___x_3343_, 1);
lean_inc_ref(v_cache_3344_);
lean_dec(v___x_3343_);
v_inferType_3345_ = lean_ctor_get(v_cache_3344_, 0);
lean_inc_ref(v_inferType_3345_);
lean_dec_ref(v_cache_3344_);
v___x_3346_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3345_, v_a_3299_);
lean_dec_ref(v_inferType_3345_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_cancelTk_x3f_3347_; 
lean_del_object(v___x_3301_);
v_cancelTk_x3f_3347_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3347_) == 1)
{
lean_object* v_val_3348_; uint8_t v___x_3349_; 
v_val_3348_ = lean_ctor_get(v_cancelTk_x3f_3347_, 0);
v___x_3349_ = l_IO_CancelToken_isSet(v_val_3348_);
if (v___x_3349_ == 0)
{
goto v___jp_3303_;
}
else
{
lean_object* v___x_3350_; lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3299_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3276_);
v___x_3350_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
goto v___jp_3303_;
}
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; 
lean_dec(v_a_3299_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3276_);
v_val_3359_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3346_, 1);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v_val_3359_);
v___x_3361_ = v___x_3301_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_val_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
v___jp_3303_:
{
lean_object* v___x_3304_; 
v___x_3304_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3276_, v___x_3281_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec_ref(v___x_3281_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; uint8_t v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
v___x_3306_ = l_Lean_Expr_hasMVar(v_a_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v___x_3304_, 0);
lean_dec(v_unused_3342_);
v___x_3308_ = v___x_3304_;
v_isShared_3309_ = v_isSharedCheck_3341_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v___x_3304_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3341_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v_cache_3311_; lean_object* v_mctx_3312_; lean_object* v_zetaDeltaFVarIds_3313_; lean_object* v_postponed_3314_; lean_object* v_diag_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3340_; 
v___x_3310_ = lean_st_ref_take(v_a_3131_);
v_cache_3311_ = lean_ctor_get(v___x_3310_, 1);
v_mctx_3312_ = lean_ctor_get(v___x_3310_, 0);
v_zetaDeltaFVarIds_3313_ = lean_ctor_get(v___x_3310_, 2);
v_postponed_3314_ = lean_ctor_get(v___x_3310_, 3);
v_diag_3315_ = lean_ctor_get(v___x_3310_, 4);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3317_ = v___x_3310_;
v_isShared_3318_ = v_isSharedCheck_3340_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_diag_3315_);
lean_inc(v_postponed_3314_);
lean_inc(v_zetaDeltaFVarIds_3313_);
lean_inc(v_cache_3311_);
lean_inc(v_mctx_3312_);
lean_dec(v___x_3310_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3340_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v_inferType_3319_; lean_object* v_funInfo_3320_; lean_object* v_synthInstance_3321_; lean_object* v_whnf_3322_; lean_object* v_defEqTrans_3323_; lean_object* v_defEqPerm_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3339_; 
v_inferType_3319_ = lean_ctor_get(v_cache_3311_, 0);
v_funInfo_3320_ = lean_ctor_get(v_cache_3311_, 1);
v_synthInstance_3321_ = lean_ctor_get(v_cache_3311_, 2);
v_whnf_3322_ = lean_ctor_get(v_cache_3311_, 3);
v_defEqTrans_3323_ = lean_ctor_get(v_cache_3311_, 4);
v_defEqPerm_3324_ = lean_ctor_get(v_cache_3311_, 5);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_cache_3311_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3326_ = v_cache_3311_;
v_isShared_3327_ = v_isSharedCheck_3339_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_defEqPerm_3324_);
lean_inc(v_defEqTrans_3323_);
lean_inc(v_whnf_3322_);
lean_inc(v_synthInstance_3321_);
lean_inc(v_funInfo_3320_);
lean_inc(v_inferType_3319_);
lean_dec(v_cache_3311_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3339_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3330_; 
lean_inc(v_a_3305_);
v___x_3328_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3319_, v_a_3299_, v_a_3305_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3328_);
v___x_3330_ = v___x_3326_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_funInfo_3320_);
lean_ctor_set(v_reuseFailAlloc_3338_, 2, v_synthInstance_3321_);
lean_ctor_set(v_reuseFailAlloc_3338_, 3, v_whnf_3322_);
lean_ctor_set(v_reuseFailAlloc_3338_, 4, v_defEqTrans_3323_);
lean_ctor_set(v_reuseFailAlloc_3338_, 5, v_defEqPerm_3324_);
v___x_3330_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 1, v___x_3330_);
v___x_3332_ = v___x_3317_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_mctx_3312_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3337_, 2, v_zetaDeltaFVarIds_3313_);
lean_ctor_set(v_reuseFailAlloc_3337_, 3, v_postponed_3314_);
lean_ctor_set(v_reuseFailAlloc_3337_, 4, v_diag_3315_);
v___x_3332_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_st_ref_set(v_a_3131_, v___x_3332_);
if (v_isShared_3309_ == 0)
{
v___x_3335_ = v___x_3308_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3305_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3305_);
lean_dec(v_a_3299_);
return v___x_3304_;
}
}
else
{
lean_dec(v_a_3299_);
return v___x_3304_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3276_);
v_a_3364_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3298_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3298_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3129_, 2);
goto v___jp_3282_;
}
}
v___jp_3282_:
{
lean_object* v_cancelTk_x3f_3283_; 
v_cancelTk_x3f_3283_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3283_) == 1)
{
lean_object* v_val_3284_; uint8_t v___x_3285_; 
v_val_3284_ = lean_ctor_get(v_cancelTk_x3f_3283_, 0);
v___x_3285_ = l_IO_CancelToken_isSet(v_val_3284_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3276_, v___x_3281_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec_ref(v___x_3281_);
return v___x_3286_;
}
else
{
lean_object* v___x_3287_; lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3276_);
v___x_3287_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
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
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3276_, v___x_3281_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec_ref(v___x_3281_);
return v___x_3296_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3372_; 
v_cacheInferType_3372_ = lean_ctor_get_uint8(v_a_3130_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3372_ == 0)
{
goto v___jp_3150_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Expr_hasMVar(v_e_3129_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
lean_inc_ref(v_e_3129_);
v___x_3374_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3439_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3439_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3439_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3419_; lean_object* v_cache_3420_; lean_object* v_inferType_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_st_ref_get(v_a_3131_);
v_cache_3420_ = lean_ctor_get(v___x_3419_, 1);
lean_inc_ref(v_cache_3420_);
lean_dec(v___x_3419_);
v_inferType_3421_ = lean_ctor_get(v_cache_3420_, 0);
lean_inc_ref(v_inferType_3421_);
lean_dec_ref(v_cache_3420_);
v___x_3422_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3421_, v_a_3375_);
lean_dec_ref(v_inferType_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_cancelTk_x3f_3423_; 
lean_del_object(v___x_3377_);
v_cancelTk_x3f_3423_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3423_) == 1)
{
lean_object* v_val_3424_; uint8_t v___x_3425_; 
v_val_3424_ = lean_ctor_get(v_cancelTk_x3f_3423_, 0);
v___x_3425_ = l_IO_CancelToken_isSet(v_val_3424_);
if (v___x_3425_ == 0)
{
goto v___jp_3379_;
}
else
{
lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_a_3375_);
lean_dec_ref_known(v_e_3129_, 3);
v___x_3426_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
goto v___jp_3379_;
}
}
else
{
lean_object* v_val_3435_; lean_object* v___x_3437_; 
lean_dec(v_a_3375_);
lean_dec_ref_known(v_e_3129_, 3);
v_val_3435_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v___x_3422_, 1);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v_val_3435_);
v___x_3437_ = v___x_3377_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_val_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
v___jp_3379_:
{
lean_object* v___x_3380_; 
v___x_3380_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; uint8_t v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
v___x_3382_ = l_Lean_Expr_hasMVar(v_a_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3418_);
v___x_3384_ = v___x_3380_;
v_isShared_3385_ = v_isSharedCheck_3417_;
goto v_resetjp_3383_;
}
else
{
lean_dec(v___x_3380_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3417_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v_cache_3387_; lean_object* v_mctx_3388_; lean_object* v_zetaDeltaFVarIds_3389_; lean_object* v_postponed_3390_; lean_object* v_diag_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3416_; 
v___x_3386_ = lean_st_ref_take(v_a_3131_);
v_cache_3387_ = lean_ctor_get(v___x_3386_, 1);
v_mctx_3388_ = lean_ctor_get(v___x_3386_, 0);
v_zetaDeltaFVarIds_3389_ = lean_ctor_get(v___x_3386_, 2);
v_postponed_3390_ = lean_ctor_get(v___x_3386_, 3);
v_diag_3391_ = lean_ctor_get(v___x_3386_, 4);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3393_ = v___x_3386_;
v_isShared_3394_ = v_isSharedCheck_3416_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_diag_3391_);
lean_inc(v_postponed_3390_);
lean_inc(v_zetaDeltaFVarIds_3389_);
lean_inc(v_cache_3387_);
lean_inc(v_mctx_3388_);
lean_dec(v___x_3386_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3416_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_inferType_3395_; lean_object* v_funInfo_3396_; lean_object* v_synthInstance_3397_; lean_object* v_whnf_3398_; lean_object* v_defEqTrans_3399_; lean_object* v_defEqPerm_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3415_; 
v_inferType_3395_ = lean_ctor_get(v_cache_3387_, 0);
v_funInfo_3396_ = lean_ctor_get(v_cache_3387_, 1);
v_synthInstance_3397_ = lean_ctor_get(v_cache_3387_, 2);
v_whnf_3398_ = lean_ctor_get(v_cache_3387_, 3);
v_defEqTrans_3399_ = lean_ctor_get(v_cache_3387_, 4);
v_defEqPerm_3400_ = lean_ctor_get(v_cache_3387_, 5);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_cache_3387_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3402_ = v_cache_3387_;
v_isShared_3403_ = v_isSharedCheck_3415_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_defEqPerm_3400_);
lean_inc(v_defEqTrans_3399_);
lean_inc(v_whnf_3398_);
lean_inc(v_synthInstance_3397_);
lean_inc(v_funInfo_3396_);
lean_inc(v_inferType_3395_);
lean_dec(v_cache_3387_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3415_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
lean_inc(v_a_3381_);
v___x_3404_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3395_, v_a_3375_, v_a_3381_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v___x_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_funInfo_3396_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_synthInstance_3397_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_whnf_3398_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_defEqTrans_3399_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v_defEqPerm_3400_);
v___x_3406_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v___x_3406_);
v___x_3408_ = v___x_3393_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_mctx_3388_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_zetaDeltaFVarIds_3389_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_postponed_3390_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v_diag_3391_);
v___x_3408_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = lean_st_ref_set(v_a_3131_, v___x_3408_);
if (v_isShared_3385_ == 0)
{
v___x_3411_ = v___x_3384_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3381_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3381_);
lean_dec(v_a_3375_);
return v___x_3380_;
}
}
else
{
lean_dec(v_a_3375_);
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref_known(v_e_3129_, 3);
v_a_3440_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3374_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3374_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
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
else
{
goto v___jp_3150_;
}
}
}
case 9:
{
lean_object* v_a_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3448_ = lean_ctor_get(v_e_3129_, 0);
lean_inc_ref(v_a_3448_);
lean_dec_ref_known(v_e_3129_, 1);
v___x_3449_ = l_Lean_Literal_type(v_a_3448_);
lean_dec_ref(v_a_3448_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
case 10:
{
lean_object* v_expr_3451_; 
v_expr_3451_ = lean_ctor_get(v_e_3129_, 1);
lean_inc_ref(v_expr_3451_);
lean_dec_ref_known(v_e_3129_, 2);
v_e_3129_ = v_expr_3451_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3453_; lean_object* v_idx_3454_; lean_object* v_struct_3455_; uint8_t v_cacheInferType_3471_; 
v_typeName_3453_ = lean_ctor_get(v_e_3129_, 0);
lean_inc(v_typeName_3453_);
v_idx_3454_ = lean_ctor_get(v_e_3129_, 1);
lean_inc(v_idx_3454_);
v_struct_3455_ = lean_ctor_get(v_e_3129_, 2);
lean_inc_ref(v_struct_3455_);
v_cacheInferType_3471_ = lean_ctor_get_uint8(v_a_3130_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3471_ == 0)
{
lean_dec_ref_known(v_e_3129_, 3);
goto v___jp_3456_;
}
else
{
uint8_t v___x_3472_; 
v___x_3472_ = l_Lean_Expr_hasMVar(v_e_3129_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3538_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3538_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3538_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3518_; lean_object* v_cache_3519_; lean_object* v_inferType_3520_; lean_object* v___x_3521_; 
v___x_3518_ = lean_st_ref_get(v_a_3131_);
v_cache_3519_ = lean_ctor_get(v___x_3518_, 1);
lean_inc_ref(v_cache_3519_);
lean_dec(v___x_3518_);
v_inferType_3520_ = lean_ctor_get(v_cache_3519_, 0);
lean_inc_ref(v_inferType_3520_);
lean_dec_ref(v_cache_3519_);
v___x_3521_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3520_, v_a_3474_);
lean_dec_ref(v_inferType_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_cancelTk_x3f_3522_; 
lean_del_object(v___x_3476_);
v_cancelTk_x3f_3522_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3522_) == 1)
{
lean_object* v_val_3523_; uint8_t v___x_3524_; 
v_val_3523_ = lean_ctor_get(v_cancelTk_x3f_3522_, 0);
v___x_3524_ = l_IO_CancelToken_isSet(v_val_3523_);
if (v___x_3524_ == 0)
{
goto v___jp_3478_;
}
else
{
lean_object* v___x_3525_; lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3474_);
lean_dec_ref(v_struct_3455_);
lean_dec(v_idx_3454_);
lean_dec(v_typeName_3453_);
v___x_3525_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
goto v___jp_3478_;
}
}
else
{
lean_object* v_val_3534_; lean_object* v___x_3536_; 
lean_dec(v_a_3474_);
lean_dec_ref(v_struct_3455_);
lean_dec(v_idx_3454_);
lean_dec(v_typeName_3453_);
v_val_3534_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v___x_3521_, 1);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_val_3534_);
v___x_3536_ = v___x_3476_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_val_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
v___jp_3478_:
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3453_, v_idx_3454_, v_struct_3455_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; uint8_t v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
v___x_3481_ = l_Lean_Expr_hasMVar(v_a_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3516_; 
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; 
v_unused_3517_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3517_);
v___x_3483_ = v___x_3479_;
v_isShared_3484_ = v_isSharedCheck_3516_;
goto v_resetjp_3482_;
}
else
{
lean_dec(v___x_3479_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3516_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v_cache_3486_; lean_object* v_mctx_3487_; lean_object* v_zetaDeltaFVarIds_3488_; lean_object* v_postponed_3489_; lean_object* v_diag_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3515_; 
v___x_3485_ = lean_st_ref_take(v_a_3131_);
v_cache_3486_ = lean_ctor_get(v___x_3485_, 1);
v_mctx_3487_ = lean_ctor_get(v___x_3485_, 0);
v_zetaDeltaFVarIds_3488_ = lean_ctor_get(v___x_3485_, 2);
v_postponed_3489_ = lean_ctor_get(v___x_3485_, 3);
v_diag_3490_ = lean_ctor_get(v___x_3485_, 4);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3492_ = v___x_3485_;
v_isShared_3493_ = v_isSharedCheck_3515_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_diag_3490_);
lean_inc(v_postponed_3489_);
lean_inc(v_zetaDeltaFVarIds_3488_);
lean_inc(v_cache_3486_);
lean_inc(v_mctx_3487_);
lean_dec(v___x_3485_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3515_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_inferType_3494_; lean_object* v_funInfo_3495_; lean_object* v_synthInstance_3496_; lean_object* v_whnf_3497_; lean_object* v_defEqTrans_3498_; lean_object* v_defEqPerm_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3514_; 
v_inferType_3494_ = lean_ctor_get(v_cache_3486_, 0);
v_funInfo_3495_ = lean_ctor_get(v_cache_3486_, 1);
v_synthInstance_3496_ = lean_ctor_get(v_cache_3486_, 2);
v_whnf_3497_ = lean_ctor_get(v_cache_3486_, 3);
v_defEqTrans_3498_ = lean_ctor_get(v_cache_3486_, 4);
v_defEqPerm_3499_ = lean_ctor_get(v_cache_3486_, 5);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_cache_3486_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3501_ = v_cache_3486_;
v_isShared_3502_ = v_isSharedCheck_3514_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_defEqPerm_3499_);
lean_inc(v_defEqTrans_3498_);
lean_inc(v_whnf_3497_);
lean_inc(v_synthInstance_3496_);
lean_inc(v_funInfo_3495_);
lean_inc(v_inferType_3494_);
lean_dec(v_cache_3486_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3514_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_inc(v_a_3480_);
v___x_3503_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3494_, v_a_3474_, v_a_3480_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3503_);
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_funInfo_3495_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v_synthInstance_3496_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v_whnf_3497_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v_defEqTrans_3498_);
lean_ctor_set(v_reuseFailAlloc_3513_, 5, v_defEqPerm_3499_);
v___x_3505_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v___x_3505_);
v___x_3507_ = v___x_3492_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_mctx_3487_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_zetaDeltaFVarIds_3488_);
lean_ctor_set(v_reuseFailAlloc_3512_, 3, v_postponed_3489_);
lean_ctor_set(v_reuseFailAlloc_3512_, 4, v_diag_3490_);
v___x_3507_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = lean_st_ref_set(v_a_3131_, v___x_3507_);
if (v_isShared_3484_ == 0)
{
v___x_3510_ = v___x_3483_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3480_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3480_);
lean_dec(v_a_3474_);
return v___x_3479_;
}
}
else
{
lean_dec(v_a_3474_);
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_struct_3455_);
lean_dec(v_idx_3454_);
lean_dec(v_typeName_3453_);
v_a_3539_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3473_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3473_);
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
lean_dec_ref_known(v_e_3129_, 3);
goto v___jp_3456_;
}
}
v___jp_3456_:
{
lean_object* v_cancelTk_x3f_3457_; 
v_cancelTk_x3f_3457_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3457_) == 1)
{
lean_object* v_val_3458_; uint8_t v___x_3459_; 
v_val_3458_ = lean_ctor_get(v_cancelTk_x3f_3457_, 0);
v___x_3459_ = l_IO_CancelToken_isSet(v_val_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3453_, v_idx_3454_, v_struct_3455_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_struct_3455_);
lean_dec(v_idx_3454_);
lean_dec(v_typeName_3453_);
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
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3453_, v_idx_3454_, v_struct_3455_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3470_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3547_; 
v_cacheInferType_3547_ = lean_ctor_get_uint8(v_a_3130_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3547_ == 0)
{
goto v___jp_3135_;
}
else
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_Expr_hasMVar(v_e_3129_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_inc_ref(v_e_3129_);
v___x_3549_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3614_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3614_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3614_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3594_; lean_object* v_cache_3595_; lean_object* v_inferType_3596_; lean_object* v___x_3597_; 
v___x_3594_ = lean_st_ref_get(v_a_3131_);
v_cache_3595_ = lean_ctor_get(v___x_3594_, 1);
lean_inc_ref(v_cache_3595_);
lean_dec(v___x_3594_);
v_inferType_3596_ = lean_ctor_get(v_cache_3595_, 0);
lean_inc_ref(v_inferType_3596_);
lean_dec_ref(v_cache_3595_);
v___x_3597_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3596_, v_a_3550_);
lean_dec_ref(v_inferType_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_cancelTk_x3f_3598_; 
lean_del_object(v___x_3552_);
v_cancelTk_x3f_3598_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3598_) == 1)
{
lean_object* v_val_3599_; uint8_t v___x_3600_; 
v_val_3599_ = lean_ctor_get(v_cancelTk_x3f_3598_, 0);
v___x_3600_ = l_IO_CancelToken_isSet(v_val_3599_);
if (v___x_3600_ == 0)
{
goto v___jp_3554_;
}
else
{
lean_object* v___x_3601_; lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_a_3550_);
lean_dec_ref(v_e_3129_);
v___x_3601_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
goto v___jp_3554_;
}
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; 
lean_dec(v_a_3550_);
lean_dec_ref(v_e_3129_);
v_val_3610_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v___x_3597_, 1);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v_val_3610_);
v___x_3612_ = v___x_3552_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_val_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
v___jp_3554_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; uint8_t v___x_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
v___x_3557_ = l_Lean_Expr_hasMVar(v_a_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3592_; 
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v___x_3555_, 0);
lean_dec(v_unused_3593_);
v___x_3559_ = v___x_3555_;
v_isShared_3560_ = v_isSharedCheck_3592_;
goto v_resetjp_3558_;
}
else
{
lean_dec(v___x_3555_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3592_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v_cache_3562_; lean_object* v_mctx_3563_; lean_object* v_zetaDeltaFVarIds_3564_; lean_object* v_postponed_3565_; lean_object* v_diag_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3591_; 
v___x_3561_ = lean_st_ref_take(v_a_3131_);
v_cache_3562_ = lean_ctor_get(v___x_3561_, 1);
v_mctx_3563_ = lean_ctor_get(v___x_3561_, 0);
v_zetaDeltaFVarIds_3564_ = lean_ctor_get(v___x_3561_, 2);
v_postponed_3565_ = lean_ctor_get(v___x_3561_, 3);
v_diag_3566_ = lean_ctor_get(v___x_3561_, 4);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3568_ = v___x_3561_;
v_isShared_3569_ = v_isSharedCheck_3591_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_diag_3566_);
lean_inc(v_postponed_3565_);
lean_inc(v_zetaDeltaFVarIds_3564_);
lean_inc(v_cache_3562_);
lean_inc(v_mctx_3563_);
lean_dec(v___x_3561_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3591_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v_inferType_3570_; lean_object* v_funInfo_3571_; lean_object* v_synthInstance_3572_; lean_object* v_whnf_3573_; lean_object* v_defEqTrans_3574_; lean_object* v_defEqPerm_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3590_; 
v_inferType_3570_ = lean_ctor_get(v_cache_3562_, 0);
v_funInfo_3571_ = lean_ctor_get(v_cache_3562_, 1);
v_synthInstance_3572_ = lean_ctor_get(v_cache_3562_, 2);
v_whnf_3573_ = lean_ctor_get(v_cache_3562_, 3);
v_defEqTrans_3574_ = lean_ctor_get(v_cache_3562_, 4);
v_defEqPerm_3575_ = lean_ctor_get(v_cache_3562_, 5);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_cache_3562_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3577_ = v_cache_3562_;
v_isShared_3578_ = v_isSharedCheck_3590_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_defEqPerm_3575_);
lean_inc(v_defEqTrans_3574_);
lean_inc(v_whnf_3573_);
lean_inc(v_synthInstance_3572_);
lean_inc(v_funInfo_3571_);
lean_inc(v_inferType_3570_);
lean_dec(v_cache_3562_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3590_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_inc(v_a_3556_);
v___x_3579_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3570_, v_a_3550_, v_a_3556_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3579_);
v___x_3581_ = v___x_3577_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_funInfo_3571_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_synthInstance_3572_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v_whnf_3573_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_defEqTrans_3574_);
lean_ctor_set(v_reuseFailAlloc_3589_, 5, v_defEqPerm_3575_);
v___x_3581_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3583_; 
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 1, v___x_3581_);
v___x_3583_ = v___x_3568_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_mctx_3563_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_zetaDeltaFVarIds_3564_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_postponed_3565_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_diag_3566_);
v___x_3583_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3584_ = lean_st_ref_set(v_a_3131_, v___x_3583_);
if (v_isShared_3560_ == 0)
{
v___x_3586_ = v___x_3559_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3556_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3556_);
lean_dec(v_a_3550_);
return v___x_3555_;
}
}
else
{
lean_dec(v_a_3550_);
return v___x_3555_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v_e_3129_);
v_a_3615_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3549_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3549_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
goto v___jp_3135_;
}
}
}
}
v___jp_3135_:
{
lean_object* v_cancelTk_x3f_3136_; 
v_cancelTk_x3f_3136_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3136_) == 1)
{
lean_object* v_val_3137_; uint8_t v___x_3138_; 
v_val_3137_ = lean_ctor_get(v_cancelTk_x3f_3136_, 0);
v___x_3138_ = l_IO_CancelToken_isSet(v_val_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_e_3129_);
v___x_3140_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3149_;
}
}
v___jp_3150_:
{
lean_object* v_cancelTk_x3f_3151_; 
v_cancelTk_x3f_3151_ = lean_ctor_get(v_a_3132_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3151_) == 1)
{
lean_object* v_val_3152_; uint8_t v___x_3153_; 
v_val_3152_ = lean_ctor_get(v_cancelTk_x3f_3151_, 0);
v___x_3153_ = l_IO_CancelToken_isSet(v_val_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_e_3129_);
v___x_3155_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v___x_3164_; 
v___x_3164_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
return v___x_3164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3631_, v_x_3632_, v_x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3636_, v_x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3639_, v_x_3640_, v_x_3641_);
lean_dec_ref(v_x_3641_);
lean_dec_ref(v_x_3640_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3643_, lean_object* v_x_3644_, size_t v_x_3645_, size_t v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3644_, v_x_3645_, v_x_3646_, v_x_3647_, v_x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3650_, lean_object* v_x_3651_, lean_object* v_x_3652_, lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_){
_start:
{
size_t v_x_4029__boxed_3656_; size_t v_x_4030__boxed_3657_; lean_object* v_res_3658_; 
v_x_4029__boxed_3656_ = lean_unbox_usize(v_x_3652_);
lean_dec(v_x_3652_);
v_x_4030__boxed_3657_ = lean_unbox_usize(v_x_3653_);
lean_dec(v_x_3653_);
v_res_3658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3650_, v_x_3651_, v_x_4029__boxed_3656_, v_x_4030__boxed_3657_, v_x_3654_, v_x_3655_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3659_, lean_object* v_x_3660_, size_t v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3660_, v_x_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_){
_start:
{
size_t v_x_4046__boxed_3668_; lean_object* v_res_3669_; 
v_x_4046__boxed_3668_ = lean_unbox_usize(v_x_3666_);
lean_dec(v_x_3666_);
v_res_3669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3664_, v_x_3665_, v_x_4046__boxed_3668_, v_x_3667_);
lean_dec_ref(v_x_3667_);
lean_dec_ref(v_x_3665_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3670_, lean_object* v_n_3671_, lean_object* v_k_3672_, lean_object* v_v_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3671_, v_k_3672_, v_v_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3675_, size_t v_depth_3676_, lean_object* v_keys_3677_, lean_object* v_vals_3678_, lean_object* v_heq_3679_, lean_object* v_i_3680_, lean_object* v_entries_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3676_, v_keys_3677_, v_vals_3678_, v_i_3680_, v_entries_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3683_, lean_object* v_depth_3684_, lean_object* v_keys_3685_, lean_object* v_vals_3686_, lean_object* v_heq_3687_, lean_object* v_i_3688_, lean_object* v_entries_3689_){
_start:
{
size_t v_depth_boxed_3690_; lean_object* v_res_3691_; 
v_depth_boxed_3690_ = lean_unbox_usize(v_depth_3684_);
lean_dec(v_depth_3684_);
v_res_3691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3683_, v_depth_boxed_3690_, v_keys_3685_, v_vals_3686_, v_heq_3687_, v_i_3688_, v_entries_3689_);
lean_dec_ref(v_vals_3686_);
lean_dec_ref(v_keys_3685_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3692_, lean_object* v_keys_3693_, lean_object* v_vals_3694_, lean_object* v_heq_3695_, lean_object* v_i_3696_, lean_object* v_k_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3693_, v_vals_3694_, v_i_3696_, v_k_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3699_, lean_object* v_keys_3700_, lean_object* v_vals_3701_, lean_object* v_heq_3702_, lean_object* v_i_3703_, lean_object* v_k_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3699_, v_keys_3700_, v_vals_3701_, v_heq_3702_, v_i_3703_, v_k_3704_);
lean_dec_ref(v_k_3704_);
lean_dec_ref(v_vals_3701_);
lean_dec_ref(v_keys_3700_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3707_, v_x_3708_, v_x_3709_, v_x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = l_Lean_maxRecDepthErrorMessage;
v___x_3718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3720_ = l_Lean_MessageData_ofFormat(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3722_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3723_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___x_3721_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3724_){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_ref_3724_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3732_, lean_object* v_ref_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3733_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_ref_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3740_, v_ref_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; uint8_t v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; uint8_t v___y_3761_; uint8_t v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v_fileName_3867_; lean_object* v_fileMap_3868_; lean_object* v_options_3869_; lean_object* v_currRecDepth_3870_; lean_object* v_maxRecDepth_3871_; lean_object* v_ref_3872_; lean_object* v_currNamespace_3873_; lean_object* v_openDecls_3874_; lean_object* v_initHeartbeats_3875_; lean_object* v_maxHeartbeats_3876_; lean_object* v_quotContext_3877_; lean_object* v_currMacroScope_3878_; uint8_t v_diag_3879_; lean_object* v_cancelTk_x3f_3880_; uint8_t v_suppressElabErrors_3881_; lean_object* v_inheritedTraceOptions_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3900_; 
v_fileName_3867_ = lean_ctor_get(v_a_3751_, 0);
v_fileMap_3868_ = lean_ctor_get(v_a_3751_, 1);
v_options_3869_ = lean_ctor_get(v_a_3751_, 2);
v_currRecDepth_3870_ = lean_ctor_get(v_a_3751_, 3);
v_maxRecDepth_3871_ = lean_ctor_get(v_a_3751_, 4);
v_ref_3872_ = lean_ctor_get(v_a_3751_, 5);
v_currNamespace_3873_ = lean_ctor_get(v_a_3751_, 6);
v_openDecls_3874_ = lean_ctor_get(v_a_3751_, 7);
v_initHeartbeats_3875_ = lean_ctor_get(v_a_3751_, 8);
v_maxHeartbeats_3876_ = lean_ctor_get(v_a_3751_, 9);
v_quotContext_3877_ = lean_ctor_get(v_a_3751_, 10);
v_currMacroScope_3878_ = lean_ctor_get(v_a_3751_, 11);
v_diag_3879_ = lean_ctor_get_uint8(v_a_3751_, sizeof(void*)*14);
v_cancelTk_x3f_3880_ = lean_ctor_get(v_a_3751_, 12);
v_suppressElabErrors_3881_ = lean_ctor_get_uint8(v_a_3751_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3882_ = lean_ctor_get(v_a_3751_, 13);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_a_3751_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3884_ = v_a_3751_;
v_isShared_3885_ = v_isSharedCheck_3900_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_inheritedTraceOptions_3882_);
lean_inc(v_cancelTk_x3f_3880_);
lean_inc(v_currMacroScope_3878_);
lean_inc(v_quotContext_3877_);
lean_inc(v_maxHeartbeats_3876_);
lean_inc(v_initHeartbeats_3875_);
lean_inc(v_openDecls_3874_);
lean_inc(v_currNamespace_3873_);
lean_inc(v_ref_3872_);
lean_inc(v_maxRecDepth_3871_);
lean_inc(v_currRecDepth_3870_);
lean_inc(v_options_3869_);
lean_inc(v_fileMap_3868_);
lean_inc(v_fileName_3867_);
lean_dec(v_a_3751_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3900_;
goto v_resetjp_3883_;
}
v___jp_3754_:
{
lean_object* v___x_3767_; uint8_t v_foApprox_3768_; uint8_t v_ctxApprox_3769_; uint8_t v_quasiPatternApprox_3770_; uint8_t v_constApprox_3771_; uint8_t v_isDefEqStuckEx_3772_; uint8_t v_unificationHints_3773_; uint8_t v_proofIrrelevance_3774_; uint8_t v_assignSyntheticOpaque_3775_; uint8_t v_offsetCnstrs_3776_; uint8_t v_transparency_3777_; uint8_t v_univApprox_3778_; uint8_t v_zetaUnused_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3793_; 
v___x_3767_ = l_Lean_Meta_Context_config(v___y_3759_);
lean_dec_ref(v___y_3759_);
v_foApprox_3768_ = lean_ctor_get_uint8(v___x_3767_, 0);
v_ctxApprox_3769_ = lean_ctor_get_uint8(v___x_3767_, 1);
v_quasiPatternApprox_3770_ = lean_ctor_get_uint8(v___x_3767_, 2);
v_constApprox_3771_ = lean_ctor_get_uint8(v___x_3767_, 3);
v_isDefEqStuckEx_3772_ = lean_ctor_get_uint8(v___x_3767_, 4);
v_unificationHints_3773_ = lean_ctor_get_uint8(v___x_3767_, 5);
v_proofIrrelevance_3774_ = lean_ctor_get_uint8(v___x_3767_, 6);
v_assignSyntheticOpaque_3775_ = lean_ctor_get_uint8(v___x_3767_, 7);
v_offsetCnstrs_3776_ = lean_ctor_get_uint8(v___x_3767_, 8);
v_transparency_3777_ = lean_ctor_get_uint8(v___x_3767_, 9);
v_univApprox_3778_ = lean_ctor_get_uint8(v___x_3767_, 11);
v_zetaUnused_3779_ = lean_ctor_get_uint8(v___x_3767_, 17);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3781_ = v___x_3767_;
v_isShared_3782_ = v_isSharedCheck_3793_;
goto v_resetjp_3780_;
}
else
{
lean_dec(v___x_3767_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3793_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
uint8_t v___x_3783_; uint8_t v___x_3784_; uint8_t v___x_3785_; lean_object* v___x_3787_; 
v___x_3783_ = 1;
v___x_3784_ = 0;
v___x_3785_ = 2;
if (v_isShared_3782_ == 0)
{
v___x_3787_ = v___x_3781_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 0, v_foApprox_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 1, v_ctxApprox_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 2, v_quasiPatternApprox_3770_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 3, v_constApprox_3771_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 4, v_isDefEqStuckEx_3772_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 5, v_unificationHints_3773_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 6, v_proofIrrelevance_3774_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 7, v_assignSyntheticOpaque_3775_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 8, v_offsetCnstrs_3776_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 9, v_transparency_3777_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 11, v_univApprox_3778_);
lean_ctor_set_uint8(v_reuseFailAlloc_3792_, 17, v_zetaUnused_3779_);
v___x_3787_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
uint64_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
lean_ctor_set_uint8(v___x_3787_, 10, v___x_3784_);
lean_ctor_set_uint8(v___x_3787_, 12, v___x_3783_);
lean_ctor_set_uint8(v___x_3787_, 13, v___x_3783_);
lean_ctor_set_uint8(v___x_3787_, 14, v___x_3785_);
lean_ctor_set_uint8(v___x_3787_, 15, v___x_3783_);
lean_ctor_set_uint8(v___x_3787_, 16, v___x_3783_);
lean_ctor_set_uint8(v___x_3787_, 18, v___x_3783_);
v___x_3788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3787_);
v___x_3789_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set_uint64(v___x_3789_, sizeof(void*)*1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v___y_3764_);
lean_ctor_set(v___x_3790_, 2, v___y_3763_);
lean_ctor_set(v___x_3790_, 3, v___y_3755_);
lean_ctor_set(v___x_3790_, 4, v___y_3757_);
lean_ctor_set(v___x_3790_, 5, v___y_3756_);
lean_ctor_set(v___x_3790_, 6, v___y_3766_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*7, v___y_3758_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*7 + 1, v___y_3762_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*7 + 2, v___y_3765_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*7 + 3, v___y_3761_);
v___x_3791_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3748_, v___x_3790_, v_a_3750_, v___y_3760_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v___y_3760_);
lean_dec(v_a_3750_);
lean_dec_ref_known(v___x_3790_, 7);
return v___x_3791_;
}
}
}
v___jp_3794_:
{
lean_object* v___x_3797_; uint8_t v_foApprox_3798_; uint8_t v_ctxApprox_3799_; uint8_t v_quasiPatternApprox_3800_; uint8_t v_constApprox_3801_; uint8_t v_isDefEqStuckEx_3802_; uint8_t v_unificationHints_3803_; uint8_t v_proofIrrelevance_3804_; uint8_t v_assignSyntheticOpaque_3805_; uint8_t v_offsetCnstrs_3806_; uint8_t v_etaStruct_3807_; uint8_t v_univApprox_3808_; uint8_t v_iota_3809_; uint8_t v_beta_3810_; uint8_t v_proj_3811_; uint8_t v_zeta_3812_; uint8_t v_zetaDelta_3813_; uint8_t v_zetaUnused_3814_; uint8_t v_zetaHave_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3866_; 
v___x_3797_ = l_Lean_Meta_Context_config(v_a_3749_);
v_foApprox_3798_ = lean_ctor_get_uint8(v___x_3797_, 0);
v_ctxApprox_3799_ = lean_ctor_get_uint8(v___x_3797_, 1);
v_quasiPatternApprox_3800_ = lean_ctor_get_uint8(v___x_3797_, 2);
v_constApprox_3801_ = lean_ctor_get_uint8(v___x_3797_, 3);
v_isDefEqStuckEx_3802_ = lean_ctor_get_uint8(v___x_3797_, 4);
v_unificationHints_3803_ = lean_ctor_get_uint8(v___x_3797_, 5);
v_proofIrrelevance_3804_ = lean_ctor_get_uint8(v___x_3797_, 6);
v_assignSyntheticOpaque_3805_ = lean_ctor_get_uint8(v___x_3797_, 7);
v_offsetCnstrs_3806_ = lean_ctor_get_uint8(v___x_3797_, 8);
v_etaStruct_3807_ = lean_ctor_get_uint8(v___x_3797_, 10);
v_univApprox_3808_ = lean_ctor_get_uint8(v___x_3797_, 11);
v_iota_3809_ = lean_ctor_get_uint8(v___x_3797_, 12);
v_beta_3810_ = lean_ctor_get_uint8(v___x_3797_, 13);
v_proj_3811_ = lean_ctor_get_uint8(v___x_3797_, 14);
v_zeta_3812_ = lean_ctor_get_uint8(v___x_3797_, 15);
v_zetaDelta_3813_ = lean_ctor_get_uint8(v___x_3797_, 16);
v_zetaUnused_3814_ = lean_ctor_get_uint8(v___x_3797_, 17);
v_zetaHave_3815_ = lean_ctor_get_uint8(v___x_3797_, 18);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3817_ = v___x_3797_;
v_isShared_3818_ = v_isSharedCheck_3866_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v___x_3797_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3866_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
uint8_t v_trackZetaDelta_3819_; lean_object* v_zetaDeltaSet_3820_; lean_object* v_lctx_3821_; lean_object* v_localInstances_3822_; lean_object* v_defEqCtx_x3f_3823_; lean_object* v_synthPendingDepth_3824_; lean_object* v_canUnfold_x3f_3825_; uint8_t v_univApprox_3826_; uint8_t v_inTypeClassResolution_3827_; uint8_t v_cacheInferType_3828_; lean_object* v_config_3830_; 
v_trackZetaDelta_3819_ = lean_ctor_get_uint8(v_a_3749_, sizeof(void*)*7);
v_zetaDeltaSet_3820_ = lean_ctor_get(v_a_3749_, 1);
lean_inc(v_zetaDeltaSet_3820_);
v_lctx_3821_ = lean_ctor_get(v_a_3749_, 2);
lean_inc_ref(v_lctx_3821_);
v_localInstances_3822_ = lean_ctor_get(v_a_3749_, 3);
lean_inc_ref(v_localInstances_3822_);
v_defEqCtx_x3f_3823_ = lean_ctor_get(v_a_3749_, 4);
lean_inc(v_defEqCtx_x3f_3823_);
v_synthPendingDepth_3824_ = lean_ctor_get(v_a_3749_, 5);
lean_inc(v_synthPendingDepth_3824_);
v_canUnfold_x3f_3825_ = lean_ctor_get(v_a_3749_, 6);
lean_inc(v_canUnfold_x3f_3825_);
v_univApprox_3826_ = lean_ctor_get_uint8(v_a_3749_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3827_ = lean_ctor_get_uint8(v_a_3749_, sizeof(void*)*7 + 2);
v_cacheInferType_3828_ = lean_ctor_get_uint8(v_a_3749_, sizeof(void*)*7 + 3);
if (v_isShared_3818_ == 0)
{
v_config_3830_ = v___x_3817_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 0, v_foApprox_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 1, v_ctxApprox_3799_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 2, v_quasiPatternApprox_3800_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 3, v_constApprox_3801_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 4, v_isDefEqStuckEx_3802_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 5, v_unificationHints_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 6, v_proofIrrelevance_3804_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 7, v_assignSyntheticOpaque_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 8, v_offsetCnstrs_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 10, v_etaStruct_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 11, v_univApprox_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 12, v_iota_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 13, v_beta_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 14, v_proj_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 15, v_zeta_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 16, v_zetaDelta_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 17, v_zetaUnused_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3865_, 18, v_zetaHave_3815_);
v_config_3830_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
uint64_t v___x_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3857_; 
lean_ctor_set_uint8(v_config_3830_, 9, v___y_3796_);
v___x_3831_ = l_Lean_Meta_Context_configKey(v_a_3749_);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_a_3749_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; lean_object* v_unused_3859_; lean_object* v_unused_3860_; lean_object* v_unused_3861_; lean_object* v_unused_3862_; lean_object* v_unused_3863_; lean_object* v_unused_3864_; 
v_unused_3858_ = lean_ctor_get(v_a_3749_, 6);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_a_3749_, 5);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_a_3749_, 4);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_a_3749_, 3);
lean_dec(v_unused_3861_);
v_unused_3862_ = lean_ctor_get(v_a_3749_, 2);
lean_dec(v_unused_3862_);
v_unused_3863_ = lean_ctor_get(v_a_3749_, 1);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_a_3749_, 0);
lean_dec(v_unused_3864_);
v___x_3833_ = v_a_3749_;
v_isShared_3834_ = v_isSharedCheck_3857_;
goto v_resetjp_3832_;
}
else
{
lean_dec(v_a_3749_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3857_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
uint64_t v___x_3835_; uint64_t v___x_3836_; uint64_t v___x_3837_; uint64_t v___x_3838_; uint64_t v_key_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3835_ = 3ULL;
v___x_3836_ = lean_uint64_shift_right(v___x_3831_, v___x_3835_);
v___x_3837_ = lean_uint64_shift_left(v___x_3836_, v___x_3835_);
v___x_3838_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3796_);
v_key_3839_ = lean_uint64_lor(v___x_3837_, v___x_3838_);
v___x_3840_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3840_, 0, v_config_3830_);
lean_ctor_set_uint64(v___x_3840_, sizeof(void*)*1, v_key_3839_);
lean_inc(v_canUnfold_x3f_3825_);
lean_inc(v_synthPendingDepth_3824_);
lean_inc(v_defEqCtx_x3f_3823_);
lean_inc_ref(v_localInstances_3822_);
lean_inc_ref(v_lctx_3821_);
lean_inc(v_zetaDeltaSet_3820_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3840_);
v___x_3842_ = v___x_3833_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_zetaDeltaSet_3820_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_lctx_3821_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_localInstances_3822_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_defEqCtx_x3f_3823_);
lean_ctor_set(v_reuseFailAlloc_3856_, 5, v_synthPendingDepth_3824_);
lean_ctor_set(v_reuseFailAlloc_3856_, 6, v_canUnfold_x3f_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3856_, sizeof(void*)*7, v_trackZetaDelta_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3856_, sizeof(void*)*7 + 1, v_univApprox_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3856_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3827_);
lean_ctor_set_uint8(v_reuseFailAlloc_3856_, sizeof(void*)*7 + 3, v_cacheInferType_3828_);
v___x_3842_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; uint8_t v_beta_3844_; 
v___x_3843_ = l_Lean_Meta_Context_config(v___x_3842_);
v_beta_3844_ = lean_ctor_get_uint8(v___x_3843_, 13);
if (v_beta_3844_ == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v_iota_3845_; 
v_iota_3845_ = lean_ctor_get_uint8(v___x_3843_, 12);
if (v_iota_3845_ == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v_zeta_3846_; 
v_zeta_3846_ = lean_ctor_get_uint8(v___x_3843_, 15);
if (v_zeta_3846_ == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v_zetaHave_3847_; 
v_zetaHave_3847_ = lean_ctor_get_uint8(v___x_3843_, 18);
if (v_zetaHave_3847_ == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v_zetaDelta_3848_; 
v_zetaDelta_3848_ = lean_ctor_get_uint8(v___x_3843_, 16);
if (v_zetaDelta_3848_ == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v_etaStruct_3849_; uint8_t v_proj_3850_; uint8_t v___x_3851_; uint8_t v___x_3852_; 
v_etaStruct_3849_ = lean_ctor_get_uint8(v___x_3843_, 10);
v_proj_3850_ = lean_ctor_get_uint8(v___x_3843_, 14);
lean_dec_ref(v___x_3843_);
v___x_3851_ = 2;
v___x_3852_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3850_, v___x_3851_);
if (v___x_3852_ == 0)
{
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
uint8_t v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = 0;
v___x_3854_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3849_, v___x_3853_);
if (v___x_3854_ == 0)
{
v___y_3755_ = v_localInstances_3822_;
v___y_3756_ = v_synthPendingDepth_3824_;
v___y_3757_ = v_defEqCtx_x3f_3823_;
v___y_3758_ = v_trackZetaDelta_3819_;
v___y_3759_ = v___x_3842_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v_cacheInferType_3828_;
v___y_3762_ = v_univApprox_3826_;
v___y_3763_ = v_lctx_3821_;
v___y_3764_ = v_zetaDeltaSet_3820_;
v___y_3765_ = v_inTypeClassResolution_3827_;
v___y_3766_ = v_canUnfold_x3f_3825_;
goto v___jp_3754_;
}
else
{
lean_object* v___x_3855_; 
lean_dec(v_canUnfold_x3f_3825_);
lean_dec(v_synthPendingDepth_3824_);
lean_dec(v_defEqCtx_x3f_3823_);
lean_dec_ref(v_localInstances_3822_);
lean_dec_ref(v_lctx_3821_);
lean_dec(v_zetaDeltaSet_3820_);
v___x_3855_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3748_, v___x_3842_, v_a_3750_, v___y_3795_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v___y_3795_);
lean_dec(v_a_3750_);
lean_dec_ref(v___x_3842_);
return v___x_3855_;
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
v_resetjp_3883_:
{
lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3896_ = lean_unsigned_to_nat(0u);
v___x_3897_ = lean_nat_dec_eq(v_maxRecDepth_3871_, v___x_3896_);
if (v___x_3897_ == 0)
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_nat_dec_eq(v_currRecDepth_3870_, v_maxRecDepth_3871_);
if (v___x_3898_ == 0)
{
goto v___jp_3886_;
}
else
{
lean_object* v___x_3899_; 
lean_del_object(v___x_3884_);
lean_dec_ref(v_inheritedTraceOptions_3882_);
lean_dec(v_cancelTk_x3f_3880_);
lean_dec(v_currMacroScope_3878_);
lean_dec(v_quotContext_3877_);
lean_dec(v_maxHeartbeats_3876_);
lean_dec(v_initHeartbeats_3875_);
lean_dec(v_openDecls_3874_);
lean_dec(v_currNamespace_3873_);
lean_dec(v_maxRecDepth_3871_);
lean_dec(v_currRecDepth_3870_);
lean_dec_ref(v_options_3869_);
lean_dec_ref(v_fileMap_3868_);
lean_dec_ref(v_fileName_3867_);
lean_dec(v_a_3752_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec_ref(v_e_3748_);
v___x_3899_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3872_);
return v___x_3899_;
}
}
else
{
goto v___jp_3886_;
}
v___jp_3886_:
{
lean_object* v___x_3887_; uint8_t v_transparency_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v___x_3887_ = l_Lean_Meta_Context_config(v_a_3749_);
v_transparency_3888_ = lean_ctor_get_uint8(v___x_3887_, 9);
lean_dec_ref(v___x_3887_);
v___x_3889_ = lean_unsigned_to_nat(1u);
v___x_3890_ = lean_nat_add(v_currRecDepth_3870_, v___x_3889_);
lean_dec(v_currRecDepth_3870_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 3, v___x_3890_);
v___x_3892_ = v___x_3884_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_fileName_3867_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_fileMap_3868_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_options_3869_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v___x_3890_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_maxRecDepth_3871_);
lean_ctor_set(v_reuseFailAlloc_3895_, 5, v_ref_3872_);
lean_ctor_set(v_reuseFailAlloc_3895_, 6, v_currNamespace_3873_);
lean_ctor_set(v_reuseFailAlloc_3895_, 7, v_openDecls_3874_);
lean_ctor_set(v_reuseFailAlloc_3895_, 8, v_initHeartbeats_3875_);
lean_ctor_set(v_reuseFailAlloc_3895_, 9, v_maxHeartbeats_3876_);
lean_ctor_set(v_reuseFailAlloc_3895_, 10, v_quotContext_3877_);
lean_ctor_set(v_reuseFailAlloc_3895_, 11, v_currMacroScope_3878_);
lean_ctor_set(v_reuseFailAlloc_3895_, 12, v_cancelTk_x3f_3880_);
lean_ctor_set(v_reuseFailAlloc_3895_, 13, v_inheritedTraceOptions_3882_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*14, v_diag_3879_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*14 + 1, v_suppressElabErrors_3881_);
v___x_3892_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
uint8_t v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = 1;
v___x_3894_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3888_, v___x_3893_);
if (v___x_3894_ == 0)
{
v___y_3795_ = v___x_3892_;
v___y_3796_ = v_transparency_3888_;
goto v___jp_3794_;
}
else
{
v___y_3795_ = v___x_3892_;
v___y_3796_ = v___x_3893_;
goto v___jp_3794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = lean_infer_type(v_e_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v_res_3907_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3908_){
_start:
{
switch(lean_obj_tag(v_x_3908_))
{
case 0:
{
uint8_t v___x_3909_; 
v___x_3909_ = 1;
return v___x_3909_;
}
case 2:
{
lean_object* v_a_3910_; lean_object* v_a_3911_; uint8_t v___x_3912_; 
v_a_3910_ = lean_ctor_get(v_x_3908_, 0);
v_a_3911_ = lean_ctor_get(v_x_3908_, 1);
v___x_3912_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3910_);
if (v___x_3912_ == 0)
{
return v___x_3912_;
}
else
{
v_x_3908_ = v_a_3911_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3914_; 
v_a_3914_ = lean_ctor_get(v_x_3908_, 1);
v_x_3908_ = v_a_3914_;
goto _start;
}
default: 
{
uint8_t v___x_3916_; 
v___x_3916_ = 0;
return v___x_3916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3917_){
_start:
{
uint8_t v_res_3918_; lean_object* v_r_3919_; 
v_res_3918_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3917_);
lean_dec(v_x_3917_);
v_r_3919_ = lean_box(v_res_3918_);
return v_r_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v_mctx_3924_; lean_object* v___x_3925_; lean_object* v_fst_3926_; lean_object* v_snd_3927_; lean_object* v___x_3928_; lean_object* v_cache_3929_; lean_object* v_zetaDeltaFVarIds_3930_; lean_object* v_postponed_3931_; lean_object* v_diag_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3941_; 
v___x_3923_ = lean_st_ref_get(v___y_3921_);
v_mctx_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_mctx_3924_);
lean_dec(v___x_3923_);
v___x_3925_ = lean_instantiate_level_mvars(v_mctx_3924_, v_l_3920_);
v_fst_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_fst_3926_);
v_snd_3927_ = lean_ctor_get(v___x_3925_, 1);
lean_inc(v_snd_3927_);
lean_dec_ref(v___x_3925_);
v___x_3928_ = lean_st_ref_take(v___y_3921_);
v_cache_3929_ = lean_ctor_get(v___x_3928_, 1);
v_zetaDeltaFVarIds_3930_ = lean_ctor_get(v___x_3928_, 2);
v_postponed_3931_ = lean_ctor_get(v___x_3928_, 3);
v_diag_3932_ = lean_ctor_get(v___x_3928_, 4);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; 
v_unused_3942_ = lean_ctor_get(v___x_3928_, 0);
lean_dec(v_unused_3942_);
v___x_3934_ = v___x_3928_;
v_isShared_3935_ = v_isSharedCheck_3941_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_diag_3932_);
lean_inc(v_postponed_3931_);
lean_inc(v_zetaDeltaFVarIds_3930_);
lean_inc(v_cache_3929_);
lean_dec(v___x_3928_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3941_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v_fst_3926_);
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_fst_3926_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_cache_3929_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_zetaDeltaFVarIds_3930_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_postponed_3931_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_diag_3932_);
v___x_3937_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_st_ref_set(v___y_3921_, v___x_3937_);
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v_snd_3927_);
return v___x_3939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3943_, v___y_3944_);
lean_dec(v___y_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3947_, v___y_3949_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
switch(lean_obj_tag(v_x_3961_))
{
case 3:
{
lean_object* v_u_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v_u_3972_ = lean_ctor_get(v_x_3961_, 0);
lean_inc(v_u_3972_);
lean_dec_ref_known(v_x_3961_, 1);
v___x_3973_ = lean_unsigned_to_nat(0u);
v___x_3974_ = lean_nat_dec_eq(v_x_3962_, v___x_3973_);
lean_dec(v_x_3962_);
if (v___x_3974_ == 0)
{
lean_dec(v_u_3972_);
goto v___jp_3968_;
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3972_, v_a_3964_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3986_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
uint8_t v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3984_; 
v___x_3980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3976_);
lean_dec(v_a_3976_);
v___x_3981_ = l_Bool_toLBool(v___x_3980_);
v___x_3982_ = lean_box(v___x_3981_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3982_);
v___x_3984_ = v___x_3978_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_a_3987_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3975_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3975_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3995_; lean_object* v_zero_3996_; uint8_t v_isZero_3997_; 
v_body_3995_ = lean_ctor_get(v_x_3961_, 2);
lean_inc_ref(v_body_3995_);
lean_dec_ref_known(v_x_3961_, 3);
v_zero_3996_ = lean_unsigned_to_nat(0u);
v_isZero_3997_ = lean_nat_dec_eq(v_x_3962_, v_zero_3996_);
if (v_isZero_3997_ == 1)
{
uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec_ref(v_body_3995_);
lean_dec(v_x_3962_);
v___x_3998_ = 0;
v___x_3999_ = lean_box(v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
else
{
lean_object* v_one_4001_; lean_object* v_n_4002_; 
v_one_4001_ = lean_unsigned_to_nat(1u);
v_n_4002_ = lean_nat_sub(v_x_3962_, v_one_4001_);
lean_dec(v_x_3962_);
v_x_3961_ = v_body_3995_;
v_x_3962_ = v_n_4002_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4004_; 
v_body_4004_ = lean_ctor_get(v_x_3961_, 3);
lean_inc_ref(v_body_4004_);
lean_dec_ref_known(v_x_3961_, 4);
v_x_3961_ = v_body_4004_;
goto _start;
}
case 10:
{
lean_object* v_expr_4006_; 
v_expr_4006_ = lean_ctor_get(v_x_3961_, 1);
lean_inc_ref(v_expr_4006_);
lean_dec_ref_known(v_x_3961_, 2);
v_x_3961_ = v_expr_4006_;
goto _start;
}
default: 
{
lean_dec(v_x_3962_);
lean_dec_ref(v_x_3961_);
goto v___jp_3968_;
}
}
v___jp_3968_:
{
uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = 2;
v___x_3970_ = lean_box(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_4008_, lean_object* v_x_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4008_, v_x_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
switch(lean_obj_tag(v_x_4016_))
{
case 4:
{
lean_object* v_declName_4023_; lean_object* v_us_4024_; lean_object* v___x_4025_; 
v_declName_4023_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_declName_4023_);
v_us_4024_ = lean_ctor_get(v_x_4016_, 1);
lean_inc(v_us_4024_);
lean_dec_ref_known(v_x_4016_, 2);
v___x_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4023_, v_us_4024_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___x_4027_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4026_, v_x_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
return v___x_4027_;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_x_4017_);
v_a_4028_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4025_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4025_);
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
case 1:
{
lean_object* v_fvarId_4036_; lean_object* v___x_4037_; 
v_fvarId_4036_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_fvarId_4036_);
lean_dec_ref_known(v_x_4016_, 1);
v___x_4037_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4036_, v_a_4018_, v_a_4020_, v_a_4021_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___x_4039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4038_, v_x_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_x_4017_);
v_a_4040_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4037_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4037_);
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
v_mvarId_4048_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_mvarId_4048_);
lean_dec_ref_known(v_x_4016_, 1);
v___x_4049_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4048_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4050_, v_x_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
return v___x_4051_;
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v_x_4017_);
v_a_4052_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4049_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4049_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
case 5:
{
lean_object* v_fn_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_fn_4060_ = lean_ctor_get(v_x_4016_, 0);
lean_inc_ref(v_fn_4060_);
lean_dec_ref_known(v_x_4016_, 2);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = lean_nat_add(v_x_4017_, v___x_4061_);
lean_dec(v_x_4017_);
v_x_4016_ = v_fn_4060_;
v_x_4017_ = v___x_4062_;
goto _start;
}
case 10:
{
lean_object* v_expr_4064_; 
v_expr_4064_ = lean_ctor_get(v_x_4016_, 1);
lean_inc_ref(v_expr_4064_);
lean_dec_ref_known(v_x_4016_, 2);
v_x_4016_ = v_expr_4064_;
goto _start;
}
case 8:
{
lean_object* v_body_4066_; 
v_body_4066_ = lean_ctor_get(v_x_4016_, 3);
lean_inc_ref(v_body_4066_);
lean_dec_ref_known(v_x_4016_, 4);
v_x_4016_ = v_body_4066_;
goto _start;
}
case 6:
{
lean_object* v_body_4068_; lean_object* v_zero_4069_; uint8_t v_isZero_4070_; 
v_body_4068_ = lean_ctor_get(v_x_4016_, 2);
lean_inc_ref(v_body_4068_);
lean_dec_ref_known(v_x_4016_, 3);
v_zero_4069_ = lean_unsigned_to_nat(0u);
v_isZero_4070_ = lean_nat_dec_eq(v_x_4017_, v_zero_4069_);
if (v_isZero_4070_ == 1)
{
uint8_t v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref(v_body_4068_);
lean_dec(v_x_4017_);
v___x_4071_ = 0;
v___x_4072_ = lean_box(v___x_4071_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
else
{
lean_object* v_one_4074_; lean_object* v_n_4075_; 
v_one_4074_ = lean_unsigned_to_nat(1u);
v_n_4075_ = lean_nat_sub(v_x_4017_, v_one_4074_);
lean_dec(v_x_4017_);
v_x_4016_ = v_body_4068_;
v_x_4017_ = v_n_4075_;
goto _start;
}
}
default: 
{
uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec(v_x_4017_);
lean_dec_ref(v_x_4016_);
v___x_4077_ = 2;
v___x_4078_ = lean_box(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4080_, v_x_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
switch(lean_obj_tag(v_x_4088_))
{
case 0:
{
uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec_ref_known(v_x_4088_, 1);
v___x_4094_ = 2;
v___x_4095_ = lean_box(v___x_4094_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
case 1:
{
lean_object* v_fvarId_4097_; lean_object* v___x_4098_; 
v_fvarId_4097_ = lean_ctor_get(v_x_4088_, 0);
lean_inc(v_fvarId_4097_);
lean_dec_ref_known(v_x_4088_, 1);
v___x_4098_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4097_, v_a_4089_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4099_, v___x_4100_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
return v___x_4101_;
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
v_a_4102_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4098_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4098_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4110_; lean_object* v___x_4111_; 
v_mvarId_4110_ = lean_ctor_get(v_x_4088_, 0);
lean_inc(v_mvarId_4110_);
lean_dec_ref_known(v_x_4088_, 1);
v___x_4111_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4110_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4112_, v___x_4113_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
return v___x_4114_;
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_a_4115_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4111_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4111_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
case 4:
{
lean_object* v_declName_4123_; lean_object* v_us_4124_; lean_object* v___x_4125_; 
v_declName_4123_ = lean_ctor_get(v_x_4088_, 0);
lean_inc(v_declName_4123_);
v_us_4124_ = lean_ctor_get(v_x_4088_, 1);
lean_inc(v_us_4124_);
lean_dec_ref_known(v_x_4088_, 2);
v___x_4125_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4123_, v_us_4124_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4126_, v___x_4127_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
return v___x_4128_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4129_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4125_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4125_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
case 5:
{
lean_object* v_fn_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v_fn_4137_ = lean_ctor_get(v_x_4088_, 0);
lean_inc_ref(v_fn_4137_);
lean_dec_ref_known(v_x_4088_, 2);
v___x_4138_ = lean_unsigned_to_nat(1u);
v___x_4139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4137_, v___x_4138_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_);
return v___x_4139_;
}
case 7:
{
lean_object* v_body_4140_; 
v_body_4140_ = lean_ctor_get(v_x_4088_, 2);
lean_inc_ref(v_body_4140_);
lean_dec_ref_known(v_x_4088_, 3);
v_x_4088_ = v_body_4140_;
goto _start;
}
case 8:
{
lean_object* v_body_4142_; 
v_body_4142_ = lean_ctor_get(v_x_4088_, 3);
lean_inc_ref(v_body_4142_);
lean_dec_ref_known(v_x_4088_, 4);
v_x_4088_ = v_body_4142_;
goto _start;
}
case 10:
{
lean_object* v_expr_4144_; 
v_expr_4144_ = lean_ctor_get(v_x_4088_, 1);
lean_inc_ref(v_expr_4144_);
lean_dec_ref_known(v_x_4088_, 2);
v_x_4088_ = v_expr_4144_;
goto _start;
}
case 11:
{
uint8_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref_known(v_x_4088_, 3);
v___x_4146_ = 2;
v___x_4147_ = lean_box(v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
default: 
{
uint8_t v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_dec_ref(v_x_4088_);
v___x_4149_ = 0;
v___x_4150_ = lean_box(v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Meta_isPropQuick(v_x_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___x_4165_; 
lean_inc_ref(v_e_4159_);
v___x_4165_ = l_Lean_Meta_isPropQuick(v_e_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4222_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4222_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4222_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
uint8_t v___x_4170_; 
v___x_4170_ = lean_unbox(v_a_4166_);
lean_dec(v_a_4166_);
switch(v___x_4170_)
{
case 0:
{
uint8_t v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
lean_dec_ref(v_e_4159_);
v___x_4171_ = 0;
v___x_4172_ = lean_box(v___x_4171_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4172_);
v___x_4174_ = v___x_4168_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
case 1:
{
uint8_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
lean_dec_ref(v_e_4159_);
v___x_4176_ = 1;
v___x_4177_ = lean_box(v___x_4176_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4177_);
v___x_4179_ = v___x_4168_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
default: 
{
lean_object* v___x_4181_; 
lean_del_object(v___x_4168_);
lean_inc(v_a_4163_);
lean_inc_ref(v_a_4162_);
lean_inc(v_a_4161_);
lean_inc_ref(v_a_4160_);
v___x_4181_ = lean_infer_type(v_e_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v___x_4183_ = l_Lean_Meta_whnfD(v_a_4182_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4205_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4205_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4205_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
if (lean_obj_tag(v_a_4184_) == 3)
{
lean_object* v_u_4188_; lean_object* v___x_4189_; lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4199_; 
lean_del_object(v___x_4186_);
v_u_4188_ = lean_ctor_get(v_a_4184_, 0);
lean_inc(v_u_4188_);
lean_dec_ref_known(v_a_4184_, 1);
v___x_4189_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4188_, v_a_4161_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4199_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4199_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4190_);
lean_dec(v_a_4190_);
v___x_4195_ = lean_box(v___x_4194_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v___x_4195_);
v___x_4197_ = v___x_4192_;
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
else
{
uint8_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4203_; 
lean_dec(v_a_4184_);
v___x_4200_ = 0;
v___x_4201_ = lean_box(v___x_4200_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4201_);
v___x_4203_ = v___x_4186_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4183_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4183_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
v_a_4214_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4181_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4181_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec_ref(v_e_4159_);
v_a_4223_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4165_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4165_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_Meta_isProp(v_e_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4238_){
_start:
{
switch(lean_obj_tag(v_x_4238_))
{
case 0:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_unsigned_to_nat(0u);
return v___x_4239_;
}
case 1:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_unsigned_to_nat(1u);
return v___x_4240_;
}
case 2:
{
lean_object* v___x_4241_; 
v___x_4241_ = lean_unsigned_to_nat(2u);
return v___x_4241_;
}
default: 
{
lean_object* v___x_4242_; 
v___x_4242_ = lean_unsigned_to_nat(3u);
return v___x_4242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4243_);
lean_dec(v_x_4243_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4245_, lean_object* v_k_4246_){
_start:
{
if (lean_obj_tag(v_t_4245_) == 3)
{
lean_object* v_idx_4247_; lean_object* v___x_4248_; 
v_idx_4247_ = lean_ctor_get(v_t_4245_, 0);
lean_inc(v_idx_4247_);
lean_dec_ref_known(v_t_4245_, 1);
v___x_4248_ = lean_apply_1(v_k_4246_, v_idx_4247_);
return v___x_4248_;
}
else
{
lean_dec(v_t_4245_);
return v_k_4246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4249_, lean_object* v_ctorIdx_4250_, lean_object* v_t_4251_, lean_object* v_h_4252_, lean_object* v_k_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4251_, v_k_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4255_, lean_object* v_ctorIdx_4256_, lean_object* v_t_4257_, lean_object* v_h_4258_, lean_object* v_k_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4255_, v_ctorIdx_4256_, v_t_4257_, v_h_4258_, v_k_4259_);
lean_dec(v_ctorIdx_4256_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4261_, lean_object* v_false_4262_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4261_, v_false_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4264_, lean_object* v_t_4265_, lean_object* v_h_4266_, lean_object* v_false_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4265_, v_false_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4269_, lean_object* v_true_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4269_, v_true_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4272_, lean_object* v_t_4273_, lean_object* v_h_4274_, lean_object* v_true_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4273_, v_true_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4277_, lean_object* v_undef_4278_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4277_, v_undef_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4280_, lean_object* v_t_4281_, lean_object* v_h_4282_, lean_object* v_undef_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4281_, v_undef_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4285_, lean_object* v_bvar_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4285_, v_bvar_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4288_, lean_object* v_t_4289_, lean_object* v_h_4290_, lean_object* v_bvar_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4289_, v_bvar_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4293_){
_start:
{
switch(v_x_4293_)
{
case 0:
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_box(0);
return v___x_4294_;
}
case 1:
{
lean_object* v___x_4295_; 
v___x_4295_ = lean_box(1);
return v___x_4295_;
}
default: 
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_box(2);
return v___x_4296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4297_){
_start:
{
uint8_t v_x_25__boxed_4298_; lean_object* v_res_4299_; 
v_x_25__boxed_4298_ = lean_unbox(v_x_4297_);
v_res_4299_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4298_);
return v_res_4299_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4300_){
_start:
{
switch(lean_obj_tag(v_x_4300_))
{
case 0:
{
uint8_t v___x_4301_; 
v___x_4301_ = 0;
return v___x_4301_;
}
case 1:
{
uint8_t v___x_4302_; 
v___x_4302_ = 1;
return v___x_4302_;
}
default: 
{
uint8_t v___x_4303_; 
v___x_4303_ = 2;
return v___x_4303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4304_){
_start:
{
uint8_t v_res_4305_; lean_object* v_r_4306_; 
v_res_4305_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4304_);
lean_dec(v_x_4304_);
v_r_4306_ = lean_box(v_res_4305_);
return v_r_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4308_){
_start:
{
switch(lean_obj_tag(v_e_4308_))
{
case 3:
{
lean_object* v_u_4309_; uint8_t v___x_4310_; 
v_u_4309_ = lean_ctor_get(v_e_4308_, 0);
v___x_4310_ = l_Lean_Level_isNeverZero(v_u_4309_);
if (v___x_4310_ == 0)
{
uint8_t v___x_4311_; 
v___x_4311_ = l_Lean_Level_isZero(v_u_4309_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_box(2);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_box(1);
return v___x_4313_;
}
}
else
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_box(0);
return v___x_4314_;
}
}
case 5:
{
lean_object* v_fn_4315_; 
v_fn_4315_ = lean_ctor_get(v_e_4308_, 0);
if (lean_obj_tag(v_fn_4315_) == 4)
{
lean_object* v_declName_4316_; 
v_declName_4316_ = lean_ctor_get(v_fn_4315_, 0);
if (lean_obj_tag(v_declName_4316_) == 1)
{
lean_object* v_pre_4317_; 
v_pre_4317_ = lean_ctor_get(v_declName_4316_, 0);
if (lean_obj_tag(v_pre_4317_) == 0)
{
lean_object* v_arg_4318_; lean_object* v_str_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; 
v_arg_4318_ = lean_ctor_get(v_e_4308_, 1);
v_str_4319_ = lean_ctor_get(v_declName_4316_, 1);
v___x_4320_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4321_ = lean_string_dec_eq(v_str_4319_, v___x_4320_);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; 
v___x_4322_ = lean_box(2);
return v___x_4322_;
}
else
{
v_e_4308_ = v_arg_4318_;
goto _start;
}
}
else
{
lean_object* v___x_4324_; 
v___x_4324_ = lean_box(2);
return v___x_4324_;
}
}
else
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_box(2);
return v___x_4325_;
}
}
else
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_box(2);
return v___x_4326_;
}
}
default: 
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_box(2);
return v___x_4327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4328_);
lean_dec_ref(v_e_4328_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4330_, lean_object* v_binderType_4331_){
_start:
{
if (lean_obj_tag(v_r_4330_) == 3)
{
lean_object* v_idx_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4344_; 
v_idx_4332_ = lean_ctor_get(v_r_4330_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_r_4330_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4334_ = v_r_4330_;
v_isShared_4335_ = v_isSharedCheck_4344_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_idx_4332_);
lean_dec(v_r_4330_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4344_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v_zero_4336_; uint8_t v_isZero_4337_; 
v_zero_4336_ = lean_unsigned_to_nat(0u);
v_isZero_4337_ = lean_nat_dec_eq(v_idx_4332_, v_zero_4336_);
if (v_isZero_4337_ == 1)
{
lean_object* v___x_4338_; 
lean_del_object(v___x_4334_);
lean_dec(v_idx_4332_);
v___x_4338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4331_);
return v___x_4338_;
}
else
{
lean_object* v_one_4339_; lean_object* v_n_4340_; lean_object* v___x_4342_; 
v_one_4339_ = lean_unsigned_to_nat(1u);
v_n_4340_ = lean_nat_sub(v_idx_4332_, v_one_4339_);
lean_dec(v_idx_4332_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v_n_4340_);
v___x_4342_ = v___x_4334_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_n_4340_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
else
{
return v_r_4330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4345_, lean_object* v_binderType_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4345_, v_binderType_4346_);
lean_dec_ref(v_binderType_4346_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4348_, lean_object* v_x_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_type_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; 
switch(lean_obj_tag(v_x_4348_))
{
case 7:
{
lean_object* v_binderType_4383_; lean_object* v_body_4384_; lean_object* v_zero_4385_; uint8_t v_isZero_4386_; 
v_binderType_4383_ = lean_ctor_get(v_x_4348_, 1);
v_body_4384_ = lean_ctor_get(v_x_4348_, 2);
v_zero_4385_ = lean_unsigned_to_nat(0u);
v_isZero_4386_ = lean_nat_dec_eq(v_x_4349_, v_zero_4385_);
if (v_isZero_4386_ == 1)
{
v_type_4356_ = v_x_4348_;
v___y_4357_ = v_a_4350_;
v___y_4358_ = v_a_4351_;
v___y_4359_ = v_a_4352_;
v___y_4360_ = v_a_4353_;
goto v___jp_4355_;
}
else
{
lean_object* v_one_4387_; lean_object* v_n_4388_; lean_object* v___x_4389_; 
lean_inc_ref(v_body_4384_);
lean_inc_ref(v_binderType_4383_);
lean_dec_ref_known(v_x_4348_, 3);
v_one_4387_ = lean_unsigned_to_nat(1u);
v_n_4388_ = lean_nat_sub(v_x_4349_, v_one_4387_);
v___x_4389_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4384_, v_n_4388_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
lean_dec(v_n_4388_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4398_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4398_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4398_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4394_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4390_, v_binderType_4383_);
lean_dec_ref(v_binderType_4383_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4394_);
v___x_4396_ = v___x_4392_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
else
{
lean_dec_ref(v_binderType_4383_);
return v___x_4389_;
}
}
}
case 8:
{
lean_object* v_type_4399_; lean_object* v_body_4400_; lean_object* v___x_4401_; 
v_type_4399_ = lean_ctor_get(v_x_4348_, 1);
lean_inc_ref(v_type_4399_);
v_body_4400_ = lean_ctor_get(v_x_4348_, 3);
lean_inc_ref(v_body_4400_);
lean_dec_ref_known(v_x_4348_, 4);
v___x_4401_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4400_, v_x_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4410_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4410_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4410_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4408_; 
v___x_4406_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4402_, v_type_4399_);
lean_dec_ref(v_type_4399_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 0, v___x_4406_);
v___x_4408_ = v___x_4404_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
else
{
lean_dec_ref(v_type_4399_);
return v___x_4401_;
}
}
case 10:
{
lean_object* v_expr_4411_; 
v_expr_4411_ = lean_ctor_get(v_x_4348_, 1);
lean_inc_ref(v_expr_4411_);
lean_dec_ref_known(v_x_4348_, 2);
v_x_4348_ = v_expr_4411_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v_deBruijnIndex_4413_ = lean_ctor_get(v_x_4348_, 0);
lean_inc(v_deBruijnIndex_4413_);
lean_dec_ref_known(v_x_4348_, 1);
v___x_4414_ = lean_unsigned_to_nat(0u);
v___x_4415_ = lean_nat_dec_eq(v_x_4349_, v___x_4414_);
if (v___x_4415_ == 0)
{
lean_dec(v_deBruijnIndex_4413_);
goto v___jp_4380_;
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4416_, 0, v_deBruijnIndex_4413_);
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
return v___x_4417_;
}
}
default: 
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = lean_unsigned_to_nat(0u);
v___x_4419_ = lean_nat_dec_eq(v_x_4349_, v___x_4418_);
if (v___x_4419_ == 0)
{
lean_dec_ref(v_x_4348_);
goto v___jp_4380_;
}
else
{
v_type_4356_ = v_x_4348_;
v___y_4357_ = v_a_4350_;
v___y_4358_ = v_a_4351_;
v___y_4359_ = v_a_4352_;
v___y_4360_ = v_a_4353_;
goto v___jp_4355_;
}
}
}
v___jp_4355_:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_Meta_isPropQuick(v_type_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
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
v___x_4366_ = lean_unbox(v_a_4362_);
lean_dec(v_a_4362_);
v___x_4367_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4366_);
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
v___jp_4380_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = lean_box(2);
v___x_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
return v___x_4382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4420_, lean_object* v_x_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4420_, v_x_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_x_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4428_, lean_object* v_n_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4428_, v_n_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4445_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4445_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4445_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
uint8_t v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4443_; 
v___x_4440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4436_);
lean_dec(v_a_4436_);
v___x_4441_ = lean_box(v___x_4440_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4441_);
v___x_4443_ = v___x_4438_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v_a_4446_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4435_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4435_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4454_, lean_object* v_n_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4454_, v_n_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
lean_dec_ref(v_a_4456_);
lean_dec(v_n_4455_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4462_, lean_object* v_x_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
switch(lean_obj_tag(v_x_4462_))
{
case 4:
{
lean_object* v_declName_4469_; lean_object* v_us_4470_; lean_object* v___x_4471_; 
v_declName_4469_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_declName_4469_);
v_us_4470_ = lean_ctor_get(v_x_4462_, 1);
lean_inc(v_us_4470_);
lean_dec_ref_known(v_x_4462_, 2);
v___x_4471_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4469_, v_us_4470_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4473_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v___x_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4472_, v_x_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_x_4463_);
return v___x_4473_;
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_x_4463_);
v_a_4474_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4471_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4471_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4482_; lean_object* v___x_4483_; 
v_fvarId_4482_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_fvarId_4482_);
lean_dec_ref_known(v_x_4462_, 1);
v___x_4483_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4482_, v_a_4464_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4484_, v_x_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_x_4463_);
return v___x_4485_;
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v_x_4463_);
v_a_4486_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4483_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4483_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4494_; lean_object* v___x_4495_; 
v_mvarId_4494_ = lean_ctor_get(v_x_4462_, 0);
lean_inc(v_mvarId_4494_);
lean_dec_ref_known(v_x_4462_, 1);
v___x_4495_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4494_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4497_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4496_, v_x_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_x_4463_);
return v___x_4497_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_x_4463_);
v_a_4498_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4495_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4495_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
case 5:
{
lean_object* v_fn_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v_fn_4506_ = lean_ctor_get(v_x_4462_, 0);
lean_inc_ref(v_fn_4506_);
lean_dec_ref_known(v_x_4462_, 2);
v___x_4507_ = lean_unsigned_to_nat(1u);
v___x_4508_ = lean_nat_add(v_x_4463_, v___x_4507_);
lean_dec(v_x_4463_);
v_x_4462_ = v_fn_4506_;
v_x_4463_ = v___x_4508_;
goto _start;
}
case 10:
{
lean_object* v_expr_4510_; 
v_expr_4510_ = lean_ctor_get(v_x_4462_, 1);
lean_inc_ref(v_expr_4510_);
lean_dec_ref_known(v_x_4462_, 2);
v_x_4462_ = v_expr_4510_;
goto _start;
}
case 8:
{
lean_object* v_body_4512_; 
v_body_4512_ = lean_ctor_get(v_x_4462_, 3);
lean_inc_ref(v_body_4512_);
lean_dec_ref_known(v_x_4462_, 4);
v_x_4462_ = v_body_4512_;
goto _start;
}
case 6:
{
lean_object* v_body_4514_; lean_object* v_zero_4515_; uint8_t v_isZero_4516_; 
v_body_4514_ = lean_ctor_get(v_x_4462_, 2);
lean_inc_ref(v_body_4514_);
lean_dec_ref_known(v_x_4462_, 3);
v_zero_4515_ = lean_unsigned_to_nat(0u);
v_isZero_4516_ = lean_nat_dec_eq(v_x_4463_, v_zero_4515_);
if (v_isZero_4516_ == 1)
{
lean_object* v___x_4517_; 
lean_dec(v_x_4463_);
v___x_4517_ = l_Lean_Meta_isProofQuick(v_body_4514_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
return v___x_4517_;
}
else
{
lean_object* v_one_4518_; lean_object* v_n_4519_; 
v_one_4518_ = lean_unsigned_to_nat(1u);
v_n_4519_ = lean_nat_sub(v_x_4463_, v_one_4518_);
lean_dec(v_x_4463_);
v_x_4462_ = v_body_4514_;
v_x_4463_ = v_n_4519_;
goto _start;
}
}
default: 
{
uint8_t v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
lean_dec(v_x_4463_);
lean_dec_ref(v_x_4462_);
v___x_4521_ = 2;
v___x_4522_ = lean_box(v___x_4521_);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
switch(lean_obj_tag(v_x_4524_))
{
case 0:
{
uint8_t v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_dec_ref_known(v_x_4524_, 1);
v___x_4530_ = 2;
v___x_4531_ = lean_box(v___x_4530_);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
return v___x_4532_;
}
case 1:
{
lean_object* v_fvarId_4533_; lean_object* v___x_4534_; 
v_fvarId_4533_ = lean_ctor_get(v_x_4524_, 0);
lean_inc(v_fvarId_4533_);
lean_dec_ref_known(v_x_4524_, 1);
v___x_4534_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4533_, v_a_4525_, v_a_4527_, v_a_4528_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___x_4536_ = lean_unsigned_to_nat(0u);
v___x_4537_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4535_, v___x_4536_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4537_;
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
v_a_4538_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4534_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4534_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4546_; lean_object* v___x_4547_; 
v_mvarId_4546_ = lean_ctor_get(v_x_4524_, 0);
lean_inc(v_mvarId_4546_);
lean_dec_ref_known(v_x_4524_, 1);
v___x_4547_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4546_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref_known(v___x_4547_, 1);
v___x_4549_ = lean_unsigned_to_nat(0u);
v___x_4550_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4548_, v___x_4549_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4550_;
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_a_4551_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4547_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4547_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
case 4:
{
lean_object* v_declName_4559_; lean_object* v_us_4560_; lean_object* v___x_4561_; 
v_declName_4559_ = lean_ctor_get(v_x_4524_, 0);
lean_inc(v_declName_4559_);
v_us_4560_ = lean_ctor_get(v_x_4524_, 1);
lean_inc(v_us_4560_);
lean_dec_ref_known(v_x_4524_, 2);
v___x_4561_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4559_, v_us_4560_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4561_, 1);
v___x_4563_ = lean_unsigned_to_nat(0u);
v___x_4564_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4562_, v___x_4563_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4564_;
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
v_a_4565_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4561_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4561_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
case 5:
{
lean_object* v_fn_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_fn_4573_ = lean_ctor_get(v_x_4524_, 0);
lean_inc_ref(v_fn_4573_);
lean_dec_ref_known(v_x_4524_, 2);
v___x_4574_ = lean_unsigned_to_nat(1u);
v___x_4575_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4573_, v___x_4574_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4575_;
}
case 6:
{
lean_object* v_body_4576_; 
v_body_4576_ = lean_ctor_get(v_x_4524_, 2);
lean_inc_ref(v_body_4576_);
lean_dec_ref_known(v_x_4524_, 3);
v_x_4524_ = v_body_4576_;
goto _start;
}
case 8:
{
lean_object* v_body_4578_; 
v_body_4578_ = lean_ctor_get(v_x_4524_, 3);
lean_inc_ref(v_body_4578_);
lean_dec_ref_known(v_x_4524_, 4);
v_x_4524_ = v_body_4578_;
goto _start;
}
case 10:
{
lean_object* v_expr_4580_; 
v_expr_4580_ = lean_ctor_get(v_x_4524_, 1);
lean_inc_ref(v_expr_4580_);
lean_dec_ref_known(v_x_4524_, 2);
v_x_4524_ = v_expr_4580_;
goto _start;
}
case 11:
{
uint8_t v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
lean_dec_ref_known(v_x_4524_, 3);
v___x_4582_ = 2;
v___x_4583_ = lean_box(v___x_4582_);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
default: 
{
uint8_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
lean_dec_ref(v_x_4524_);
v___x_4585_ = 0;
v___x_4586_ = lean_box(v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Meta_isProofQuick(v_x_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4595_, lean_object* v_x_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4595_, v_x_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v___x_4609_; 
lean_inc_ref(v_e_4603_);
v___x_4609_ = l_Lean_Meta_isProofQuick(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4636_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4636_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4636_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
uint8_t v___x_4614_; 
v___x_4614_ = lean_unbox(v_a_4610_);
lean_dec(v_a_4610_);
switch(v___x_4614_)
{
case 0:
{
uint8_t v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
lean_dec_ref(v_e_4603_);
v___x_4615_ = 0;
v___x_4616_ = lean_box(v___x_4615_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4616_);
v___x_4618_ = v___x_4612_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
case 1:
{
uint8_t v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
lean_dec_ref(v_e_4603_);
v___x_4620_ = 1;
v___x_4621_ = lean_box(v___x_4620_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4621_);
v___x_4623_ = v___x_4612_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
default: 
{
lean_object* v___x_4625_; 
lean_del_object(v___x_4612_);
lean_inc(v_a_4607_);
lean_inc_ref(v_a_4606_);
lean_inc(v_a_4605_);
lean_inc_ref(v_a_4604_);
v___x_4625_ = lean_infer_type(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4627_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref_known(v___x_4625_, 1);
v___x_4627_ = l_Lean_Meta_isProp(v_a_4626_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
return v___x_4627_;
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
v_a_4628_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4625_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4625_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v_e_4603_);
v_a_4637_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4609_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4609_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_Meta_isProof(v_e_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4652_, lean_object* v_x_4653_){
_start:
{
switch(lean_obj_tag(v_x_4652_))
{
case 3:
{
lean_object* v___x_4659_; uint8_t v___x_4660_; 
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = lean_nat_dec_eq(v_x_4653_, v___x_4659_);
lean_dec(v_x_4653_);
if (v___x_4660_ == 0)
{
goto v___jp_4655_;
}
else
{
uint8_t v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = 1;
v___x_4662_ = lean_box(v___x_4661_);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
case 7:
{
lean_object* v_body_4664_; lean_object* v_zero_4665_; uint8_t v_isZero_4666_; 
v_body_4664_ = lean_ctor_get(v_x_4652_, 2);
v_zero_4665_ = lean_unsigned_to_nat(0u);
v_isZero_4666_ = lean_nat_dec_eq(v_x_4653_, v_zero_4665_);
if (v_isZero_4666_ == 1)
{
uint8_t v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
lean_dec(v_x_4653_);
v___x_4667_ = 0;
v___x_4668_ = lean_box(v___x_4667_);
v___x_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
return v___x_4669_;
}
else
{
lean_object* v_one_4670_; lean_object* v_n_4671_; 
v_one_4670_ = lean_unsigned_to_nat(1u);
v_n_4671_ = lean_nat_sub(v_x_4653_, v_one_4670_);
lean_dec(v_x_4653_);
v_x_4652_ = v_body_4664_;
v_x_4653_ = v_n_4671_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4673_; 
v_body_4673_ = lean_ctor_get(v_x_4652_, 3);
v_x_4652_ = v_body_4673_;
goto _start;
}
case 10:
{
lean_object* v_expr_4675_; 
v_expr_4675_ = lean_ctor_get(v_x_4652_, 1);
v_x_4652_ = v_expr_4675_;
goto _start;
}
default: 
{
lean_dec(v_x_4653_);
goto v___jp_4655_;
}
}
v___jp_4655_:
{
uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4656_ = 2;
v___x_4657_ = lean_box(v___x_4656_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4677_, lean_object* v_x_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4677_, v_x_4678_);
lean_dec_ref(v_x_4677_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4681_, lean_object* v_x_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4681_, v_x_4682_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4689_, lean_object* v_x_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4689_, v_x_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec_ref(v_x_4689_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4697_, lean_object* v_x_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
switch(lean_obj_tag(v_x_4697_))
{
case 4:
{
lean_object* v_declName_4704_; lean_object* v_us_4705_; lean_object* v___x_4706_; 
v_declName_4704_ = lean_ctor_get(v_x_4697_, 0);
lean_inc(v_declName_4704_);
v_us_4705_ = lean_ctor_get(v_x_4697_, 1);
lean_inc(v_us_4705_);
lean_dec_ref_known(v_x_4697_, 2);
v___x_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4704_, v_us_4705_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v___x_4708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4707_, v_x_4698_);
lean_dec(v_a_4707_);
return v___x_4708_;
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec(v_x_4698_);
v_a_4709_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4706_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4706_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4717_; lean_object* v___x_4718_; 
v_fvarId_4717_ = lean_ctor_get(v_x_4697_, 0);
lean_inc(v_fvarId_4717_);
lean_dec_ref_known(v_x_4697_, 1);
v___x_4718_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4717_, v_a_4699_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
v___x_4720_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4719_, v_x_4698_);
lean_dec(v_a_4719_);
return v___x_4720_;
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec(v_x_4698_);
v_a_4721_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4718_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4718_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4729_; lean_object* v___x_4730_; 
v_mvarId_4729_ = lean_ctor_get(v_x_4697_, 0);
lean_inc(v_mvarId_4729_);
lean_dec_ref_known(v_x_4697_, 1);
v___x_4730_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4729_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4732_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v___x_4732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4731_, v_x_4698_);
lean_dec(v_a_4731_);
return v___x_4732_;
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec(v_x_4698_);
v_a_4733_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4730_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4730_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
case 5:
{
lean_object* v_fn_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_fn_4741_ = lean_ctor_get(v_x_4697_, 0);
lean_inc_ref(v_fn_4741_);
lean_dec_ref_known(v_x_4697_, 2);
v___x_4742_ = lean_unsigned_to_nat(1u);
v___x_4743_ = lean_nat_add(v_x_4698_, v___x_4742_);
lean_dec(v_x_4698_);
v_x_4697_ = v_fn_4741_;
v_x_4698_ = v___x_4743_;
goto _start;
}
case 10:
{
lean_object* v_expr_4745_; 
v_expr_4745_ = lean_ctor_get(v_x_4697_, 1);
lean_inc_ref(v_expr_4745_);
lean_dec_ref_known(v_x_4697_, 2);
v_x_4697_ = v_expr_4745_;
goto _start;
}
case 8:
{
lean_object* v_body_4747_; 
v_body_4747_ = lean_ctor_get(v_x_4697_, 3);
lean_inc_ref(v_body_4747_);
lean_dec_ref_known(v_x_4697_, 4);
v_x_4697_ = v_body_4747_;
goto _start;
}
case 6:
{
lean_object* v_body_4749_; lean_object* v_zero_4750_; uint8_t v_isZero_4751_; 
v_body_4749_ = lean_ctor_get(v_x_4697_, 2);
lean_inc_ref(v_body_4749_);
lean_dec_ref_known(v_x_4697_, 3);
v_zero_4750_ = lean_unsigned_to_nat(0u);
v_isZero_4751_ = lean_nat_dec_eq(v_x_4698_, v_zero_4750_);
if (v_isZero_4751_ == 1)
{
uint8_t v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
lean_dec_ref(v_body_4749_);
lean_dec(v_x_4698_);
v___x_4752_ = 0;
v___x_4753_ = lean_box(v___x_4752_);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
else
{
lean_object* v_one_4755_; lean_object* v_n_4756_; 
v_one_4755_ = lean_unsigned_to_nat(1u);
v_n_4756_ = lean_nat_sub(v_x_4698_, v_one_4755_);
lean_dec(v_x_4698_);
v_x_4697_ = v_body_4749_;
v_x_4698_ = v_n_4756_;
goto _start;
}
}
default: 
{
uint8_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec(v_x_4698_);
lean_dec_ref(v_x_4697_);
v___x_4758_ = 2;
v___x_4759_ = lean_box(v___x_4758_);
v___x_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
return v___x_4760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4761_, lean_object* v_x_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4761_, v_x_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
switch(lean_obj_tag(v_x_4769_))
{
case 1:
{
lean_object* v_fvarId_4775_; lean_object* v___x_4776_; 
v_fvarId_4775_ = lean_ctor_get(v_x_4769_, 0);
lean_inc(v_fvarId_4775_);
lean_dec_ref_known(v_x_4769_, 1);
v___x_4776_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4775_, v_a_4770_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4776_, 1);
v___x_4778_ = lean_unsigned_to_nat(0u);
v___x_4779_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4777_, v___x_4778_);
lean_dec(v_a_4777_);
return v___x_4779_;
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
v_a_4780_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4776_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4776_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4788_; lean_object* v___x_4789_; 
v_mvarId_4788_ = lean_ctor_get(v_x_4769_, 0);
lean_inc(v_mvarId_4788_);
lean_dec_ref_known(v_x_4769_, 1);
v___x_4789_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4788_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v___x_4789_, 1);
v___x_4791_ = lean_unsigned_to_nat(0u);
v___x_4792_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4790_, v___x_4791_);
lean_dec(v_a_4790_);
return v___x_4792_;
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
v_a_4793_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4789_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4789_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
case 3:
{
uint8_t v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
lean_dec_ref_known(v_x_4769_, 1);
v___x_4801_ = 1;
v___x_4802_ = lean_box(v___x_4801_);
v___x_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
return v___x_4803_;
}
case 4:
{
lean_object* v_declName_4804_; lean_object* v_us_4805_; lean_object* v___x_4806_; 
v_declName_4804_ = lean_ctor_get(v_x_4769_, 0);
lean_inc(v_declName_4804_);
v_us_4805_ = lean_ctor_get(v_x_4769_, 1);
lean_inc(v_us_4805_);
lean_dec_ref_known(v_x_4769_, 2);
v___x_4806_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4804_, v_us_4805_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
lean_inc(v_a_4807_);
lean_dec_ref_known(v___x_4806_, 1);
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4807_, v___x_4808_);
lean_dec(v_a_4807_);
return v___x_4809_;
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
v_a_4810_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4806_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4806_);
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
case 5:
{
lean_object* v_fn_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_fn_4818_ = lean_ctor_get(v_x_4769_, 0);
lean_inc_ref(v_fn_4818_);
lean_dec_ref_known(v_x_4769_, 2);
v___x_4819_ = lean_unsigned_to_nat(1u);
v___x_4820_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4818_, v___x_4819_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
return v___x_4820_;
}
case 6:
{
uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
lean_dec_ref_known(v_x_4769_, 3);
v___x_4821_ = 0;
v___x_4822_ = lean_box(v___x_4821_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
return v___x_4823_;
}
case 7:
{
uint8_t v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec_ref_known(v_x_4769_, 3);
v___x_4824_ = 1;
v___x_4825_ = lean_box(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
case 8:
{
lean_object* v_body_4827_; 
v_body_4827_ = lean_ctor_get(v_x_4769_, 3);
lean_inc_ref(v_body_4827_);
lean_dec_ref_known(v_x_4769_, 4);
v_x_4769_ = v_body_4827_;
goto _start;
}
case 9:
{
uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
lean_dec_ref_known(v_x_4769_, 1);
v___x_4829_ = 0;
v___x_4830_ = lean_box(v___x_4829_);
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
case 10:
{
lean_object* v_expr_4832_; 
v_expr_4832_ = lean_ctor_get(v_x_4769_, 1);
lean_inc_ref(v_expr_4832_);
lean_dec_ref_known(v_x_4769_, 2);
v_x_4769_ = v_expr_4832_;
goto _start;
}
default: 
{
uint8_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
lean_dec_ref(v_x_4769_);
v___x_4834_ = 2;
v___x_4835_ = lean_box(v___x_4834_);
v___x_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
return v___x_4836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_Meta_isTypeQuick(v_x_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v___x_4850_; 
lean_inc_ref(v_e_4844_);
v___x_4850_ = l_Lean_Meta_isTypeQuick(v_e_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4900_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4900_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4900_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
uint8_t v___x_4855_; 
v___x_4855_ = lean_unbox(v_a_4851_);
lean_dec(v_a_4851_);
switch(v___x_4855_)
{
case 0:
{
uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
lean_dec_ref(v_e_4844_);
v___x_4856_ = 0;
v___x_4857_ = lean_box(v___x_4856_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4857_);
v___x_4859_ = v___x_4853_;
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
case 1:
{
uint8_t v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4864_; 
lean_dec_ref(v_e_4844_);
v___x_4861_ = 1;
v___x_4862_ = lean_box(v___x_4861_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4862_);
v___x_4864_ = v___x_4853_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4862_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
default: 
{
lean_object* v___x_4866_; 
lean_del_object(v___x_4853_);
lean_inc(v_a_4848_);
lean_inc_ref(v_a_4847_);
lean_inc(v_a_4846_);
lean_inc_ref(v_a_4845_);
v___x_4866_ = lean_infer_type(v_e_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v___x_4868_ = l_Lean_Meta_whnfD(v_a_4867_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4883_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4871_ = v___x_4868_;
v_isShared_4872_ = v_isSharedCheck_4883_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4868_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4883_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
if (lean_obj_tag(v_a_4869_) == 3)
{
uint8_t v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
lean_dec_ref_known(v_a_4869_, 1);
v___x_4873_ = 1;
v___x_4874_ = lean_box(v___x_4873_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4874_);
v___x_4876_ = v___x_4871_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
else
{
uint8_t v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
lean_dec(v_a_4869_);
v___x_4878_ = 0;
v___x_4879_ = lean_box(v___x_4878_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4879_);
v___x_4881_ = v___x_4871_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4884_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4868_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4868_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
v_a_4892_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4866_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4866_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
lean_dec_ref(v_e_4844_);
v_a_4901_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4850_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4850_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Meta_isType(v_e_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
lean_dec(v_a_4913_);
lean_dec_ref(v_a_4912_);
lean_dec(v_a_4911_);
lean_dec_ref(v_a_4910_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4916_){
_start:
{
switch(lean_obj_tag(v_x_4916_))
{
case 7:
{
lean_object* v_body_4917_; 
v_body_4917_ = lean_ctor_get(v_x_4916_, 2);
v_x_4916_ = v_body_4917_;
goto _start;
}
case 3:
{
lean_object* v_u_4919_; lean_object* v___x_4920_; 
v_u_4919_ = lean_ctor_get(v_x_4916_, 0);
lean_inc(v_u_4919_);
v___x_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4920_, 0, v_u_4919_);
return v___x_4920_;
}
default: 
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_box(0);
return v___x_4921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4922_);
lean_dec_ref(v_x_4922_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4924_, lean_object* v_body_4925_, lean_object* v_x_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4924_, v_body_4925_, v_x_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4935_, lean_object* v_xs_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
switch(lean_obj_tag(v_type_4935_))
{
case 3:
{
lean_object* v_u_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_dec_ref(v_xs_4936_);
v_u_4942_ = lean_ctor_get(v_type_4935_, 0);
lean_inc(v_u_4942_);
lean_dec_ref_known(v_type_4935_, 1);
v___x_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_u_4942_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
return v___x_4944_;
}
case 7:
{
lean_object* v_binderName_4945_; lean_object* v_binderType_4946_; lean_object* v_body_4947_; uint8_t v_binderInfo_4948_; lean_object* v___f_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_binderName_4945_ = lean_ctor_get(v_type_4935_, 0);
lean_inc(v_binderName_4945_);
v_binderType_4946_ = lean_ctor_get(v_type_4935_, 1);
lean_inc_ref(v_binderType_4946_);
v_body_4947_ = lean_ctor_get(v_type_4935_, 2);
lean_inc_ref(v_body_4947_);
v_binderInfo_4948_ = lean_ctor_get_uint8(v_type_4935_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4935_, 3);
lean_inc_ref(v_xs_4936_);
v___f_4949_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4949_, 0, v_xs_4936_);
lean_closure_set(v___f_4949_, 1, v_body_4947_);
v___x_4950_ = lean_expr_instantiate_rev(v_binderType_4946_, v_xs_4936_);
lean_dec_ref(v_xs_4936_);
lean_dec_ref(v_binderType_4946_);
v___x_4951_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4945_, v_binderInfo_4948_, v___x_4950_, v___f_4949_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
return v___x_4951_;
}
default: 
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = lean_expr_instantiate_rev(v_type_4935_, v_xs_4936_);
lean_dec_ref(v_xs_4936_);
lean_dec_ref(v_type_4935_);
v___x_4953_ = l_Lean_Meta_whnfD(v___x_4952_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4969_; 
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4956_ = v___x_4953_;
v_isShared_4957_ = v_isSharedCheck_4969_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4953_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4969_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
switch(lean_obj_tag(v_a_4954_))
{
case 3:
{
lean_object* v_u_4958_; lean_object* v___x_4959_; lean_object* v___x_4961_; 
v_u_4958_ = lean_ctor_get(v_a_4954_, 0);
lean_inc(v_u_4958_);
lean_dec_ref_known(v_a_4954_, 1);
v___x_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4959_, 0, v_u_4958_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v___x_4959_);
v___x_4961_ = v___x_4956_;
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
case 7:
{
lean_object* v___x_4963_; 
lean_del_object(v___x_4956_);
v___x_4963_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4935_ = v_a_4954_;
v_xs_4936_ = v___x_4963_;
goto _start;
}
default: 
{
lean_object* v___x_4965_; lean_object* v___x_4967_; 
lean_dec(v_a_4954_);
v___x_4965_ = lean_box(0);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v___x_4965_);
v___x_4967_ = v___x_4956_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
v_a_4970_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4953_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4953_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4978_, lean_object* v_body_4979_, lean_object* v_x_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4986_ = lean_array_push(v_xs_4978_, v_x_4980_);
v___x_4987_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4979_, v___x_4986_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4988_, lean_object* v_xs_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4988_, v_xs_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4996_, lean_object* v_cache_4997_, lean_object* v_a_x3f_4998_){
_start:
{
lean_object* v___x_5000_; lean_object* v_mctx_5001_; lean_object* v_zetaDeltaFVarIds_5002_; lean_object* v_postponed_5003_; lean_object* v_diag_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5014_; 
v___x_5000_ = lean_st_ref_take(v_a_4996_);
v_mctx_5001_ = lean_ctor_get(v___x_5000_, 0);
v_zetaDeltaFVarIds_5002_ = lean_ctor_get(v___x_5000_, 2);
v_postponed_5003_ = lean_ctor_get(v___x_5000_, 3);
v_diag_5004_ = lean_ctor_get(v___x_5000_, 4);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; 
v_unused_5015_ = lean_ctor_get(v___x_5000_, 1);
lean_dec(v_unused_5015_);
v___x_5006_ = v___x_5000_;
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_diag_5004_);
lean_inc(v_postponed_5003_);
lean_inc(v_zetaDeltaFVarIds_5002_);
lean_inc(v_mctx_5001_);
lean_dec(v___x_5000_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 1, v_cache_4997_);
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_mctx_5001_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v_cache_4997_);
lean_ctor_set(v_reuseFailAlloc_5013_, 2, v_zetaDeltaFVarIds_5002_);
lean_ctor_set(v_reuseFailAlloc_5013_, 3, v_postponed_5003_);
lean_ctor_set(v_reuseFailAlloc_5013_, 4, v_diag_5004_);
v___x_5009_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = lean_st_ref_set(v_a_4996_, v___x_5009_);
v___x_5011_ = lean_box(0);
v___x_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
return v___x_5012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5016_, lean_object* v_cache_5017_, lean_object* v_a_x3f_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5016_, v_cache_5017_, v_a_x3f_5018_);
lean_dec(v_a_x3f_5018_);
lean_dec(v_a_5016_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5021_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v___x_5028_; lean_object* v_cache_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = lean_st_ref_get(v_a_5023_);
v_cache_5029_ = lean_ctor_get(v___x_5028_, 1);
lean_inc_ref(v_cache_5029_);
lean_dec(v___x_5028_);
v___x_5030_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5031_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5021_, v___x_5030_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5048_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5048_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5048_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
lean_inc(v_a_5032_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set_tag(v___x_5034_, 1);
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
v___x_5038_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5023_, v_cache_5029_, v___x_5037_);
lean_dec_ref(v___x_5037_);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5045_ == 0)
{
lean_object* v_unused_5046_; 
v_unused_5046_ = lean_ctor_get(v___x_5038_, 0);
lean_dec(v_unused_5046_);
v___x_5040_ = v___x_5038_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_dec(v___x_5038_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v_a_5032_);
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5032_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5058_; 
v_a_5049_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5050_ = lean_box(0);
v___x_5051_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5023_, v_cache_5029_, v___x_5050_);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5058_ == 0)
{
lean_object* v_unused_5059_; 
v_unused_5059_ = lean_ctor_get(v___x_5051_, 0);
lean_dec(v_unused_5059_);
v___x_5053_ = v___x_5051_;
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
else
{
lean_dec(v___x_5051_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set_tag(v___x_5053_, 1);
lean_ctor_set(v___x_5053_, 0, v_a_5049_);
v___x_5056_ = v___x_5053_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5049_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
else
{
lean_object* v___x_5060_; 
lean_dec_ref(v_type_5021_);
v___x_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5027_);
return v___x_5060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5089_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5077_ = v___x_5074_;
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5074_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
if (lean_obj_tag(v_a_5075_) == 0)
{
uint8_t v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___x_5079_ = 0;
v___x_5080_ = lean_box(v___x_5079_);
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 0, v___x_5080_);
v___x_5082_ = v___x_5077_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
else
{
uint8_t v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5087_; 
lean_dec_ref_known(v_a_5075_, 1);
v___x_5084_ = 1;
v___x_5085_ = lean_box(v___x_5084_);
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 0, v___x_5085_);
v___x_5087_ = v___x_5077_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
v_a_5090_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5074_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5074_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Lean_Meta_isTypeFormerType(v_type_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
return v_res_5104_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5105_, lean_object* v_x_5106_){
_start:
{
if (lean_obj_tag(v_x_5105_) == 0)
{
if (lean_obj_tag(v_x_5106_) == 0)
{
uint8_t v___x_5107_; 
v___x_5107_ = 1;
return v___x_5107_;
}
else
{
uint8_t v___x_5108_; 
v___x_5108_ = 0;
return v___x_5108_;
}
}
else
{
if (lean_obj_tag(v_x_5106_) == 0)
{
uint8_t v___x_5109_; 
v___x_5109_ = 0;
return v___x_5109_;
}
else
{
lean_object* v_val_5110_; lean_object* v_val_5111_; uint8_t v___x_5112_; 
v_val_5110_ = lean_ctor_get(v_x_5105_, 0);
v_val_5111_ = lean_ctor_get(v_x_5106_, 0);
v___x_5112_ = lean_level_eq(v_val_5110_, v_val_5111_);
return v___x_5112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5113_, lean_object* v_x_5114_){
_start:
{
uint8_t v_res_5115_; lean_object* v_r_5116_; 
v_res_5115_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5113_, v_x_5114_);
lean_dec(v_x_5114_);
lean_dec(v_x_5113_);
v_r_5116_ = lean_box(v_res_5115_);
return v_r_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v___x_5125_; 
v___x_5125_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5136_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5136_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5136_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5130_; uint8_t v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5134_; 
v___x_5130_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5131_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5126_, v___x_5130_);
lean_dec(v_a_5126_);
v___x_5132_ = lean_box(v___x_5131_);
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5132_);
v___x_5134_ = v___x_5128_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v___x_5132_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_a_5137_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5125_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5125_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l_Lean_Meta_isPropFormerType(v_type_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v___x_5158_; 
lean_inc(v_a_5156_);
lean_inc_ref(v_a_5155_);
lean_inc(v_a_5154_);
lean_inc_ref(v_a_5153_);
v___x_5158_ = lean_infer_type(v_e_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v_a_5159_; lean_object* v___x_5160_; 
v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
lean_inc(v_a_5159_);
lean_dec_ref_known(v___x_5158_, 1);
v___x_5160_ = l_Lean_Meta_isTypeFormerType(v_a_5159_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
return v___x_5160_;
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
v_a_5161_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5158_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5158_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_Meta_isTypeFormer(v_e_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5176_, lean_object* v_maxFVars_x3f_5177_, lean_object* v_k_5178_, uint8_t v_cleanupAnnotations_5179_, uint8_t v_whnfType_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v___f_5186_; lean_object* v___x_5187_; 
v___f_5186_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5186_, 0, v_k_5178_);
v___x_5187_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5176_, v_maxFVars_x3f_5177_, v___f_5186_, v_cleanupAnnotations_5179_, v_whnfType_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5187_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5187_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
v_a_5196_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5187_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5187_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5204_, lean_object* v_maxFVars_x3f_5205_, lean_object* v_k_5206_, lean_object* v_cleanupAnnotations_5207_, lean_object* v_whnfType_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5214_; uint8_t v_whnfType_boxed_5215_; lean_object* v_res_5216_; 
v_cleanupAnnotations_boxed_5214_ = lean_unbox(v_cleanupAnnotations_5207_);
v_whnfType_boxed_5215_ = lean_unbox(v_whnfType_5208_);
v_res_5216_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5204_, v_maxFVars_x3f_5205_, v_k_5206_, v_cleanupAnnotations_boxed_5214_, v_whnfType_boxed_5215_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5217_, lean_object* v_type_5218_, lean_object* v_maxFVars_x3f_5219_, lean_object* v_k_5220_, uint8_t v_cleanupAnnotations_5221_, uint8_t v_whnfType_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v___x_5228_; 
v___x_5228_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5218_, v_maxFVars_x3f_5219_, v_k_5220_, v_cleanupAnnotations_5221_, v_whnfType_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5229_, lean_object* v_type_5230_, lean_object* v_maxFVars_x3f_5231_, lean_object* v_k_5232_, lean_object* v_cleanupAnnotations_5233_, lean_object* v_whnfType_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5240_; uint8_t v_whnfType_boxed_5241_; lean_object* v_res_5242_; 
v_cleanupAnnotations_boxed_5240_ = lean_unbox(v_cleanupAnnotations_5233_);
v_whnfType_boxed_5241_ = lean_unbox(v_whnfType_5234_);
v_res_5242_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5229_, v_type_5230_, v_maxFVars_x3f_5231_, v_k_5232_, v_cleanupAnnotations_boxed_5240_, v_whnfType_boxed_5241_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
return v_res_5242_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5243_, lean_object* v_as_5244_, size_t v_i_5245_, size_t v_stop_5246_){
_start:
{
uint8_t v___x_5247_; 
v___x_5247_ = lean_usize_dec_eq(v_i_5245_, v_stop_5246_);
if (v___x_5247_ == 0)
{
lean_object* v___x_5248_; uint8_t v___x_5249_; 
v___x_5248_ = lean_array_uget_borrowed(v_as_5244_, v_i_5245_);
v___x_5249_ = lean_expr_eqv(v_a_5243_, v___x_5248_);
if (v___x_5249_ == 0)
{
size_t v___x_5250_; size_t v___x_5251_; 
v___x_5250_ = ((size_t)1ULL);
v___x_5251_ = lean_usize_add(v_i_5245_, v___x_5250_);
v_i_5245_ = v___x_5251_;
goto _start;
}
else
{
return v___x_5249_;
}
}
else
{
uint8_t v___x_5253_; 
v___x_5253_ = 0;
return v___x_5253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5254_, lean_object* v_as_5255_, lean_object* v_i_5256_, lean_object* v_stop_5257_){
_start:
{
size_t v_i_boxed_5258_; size_t v_stop_boxed_5259_; uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_i_boxed_5258_ = lean_unbox_usize(v_i_5256_);
lean_dec(v_i_5256_);
v_stop_boxed_5259_ = lean_unbox_usize(v_stop_5257_);
lean_dec(v_stop_5257_);
v_res_5260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5254_, v_as_5255_, v_i_boxed_5258_, v_stop_boxed_5259_);
lean_dec_ref(v_as_5255_);
lean_dec_ref(v_a_5254_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v___x_5264_; lean_object* v___x_5265_; uint8_t v___x_5266_; 
v___x_5264_ = lean_unsigned_to_nat(0u);
v___x_5265_ = lean_array_get_size(v_as_5262_);
v___x_5266_ = lean_nat_dec_lt(v___x_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
return v___x_5266_;
}
else
{
if (v___x_5266_ == 0)
{
return v___x_5266_;
}
else
{
size_t v___x_5267_; size_t v___x_5268_; uint8_t v___x_5269_; 
v___x_5267_ = ((size_t)0ULL);
v___x_5268_ = lean_usize_of_nat(v___x_5265_);
v___x_5269_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5263_, v_as_5262_, v___x_5267_, v___x_5268_);
return v___x_5269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5270_, lean_object* v_a_5271_){
_start:
{
uint8_t v_res_5272_; lean_object* v_r_5273_; 
v_res_5272_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5270_, v_a_5271_);
lean_dec_ref(v_a_5271_);
lean_dec_ref(v_as_5270_);
v_r_5273_ = lean_box(v_res_5272_);
return v_r_5273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5274_, lean_object* v_e_5275_){
_start:
{
uint8_t v___x_5276_; lean_object* v_d_5278_; lean_object* v_b_5279_; 
v___x_5276_ = l_Lean_Expr_hasFVar(v_e_5275_);
if (v___x_5276_ == 0)
{
lean_dec_ref(v_e_5275_);
return v___x_5276_;
}
else
{
switch(lean_obj_tag(v_e_5275_))
{
case 7:
{
lean_object* v_binderType_5282_; lean_object* v_body_5283_; 
v_binderType_5282_ = lean_ctor_get(v_e_5275_, 1);
lean_inc_ref(v_binderType_5282_);
v_body_5283_ = lean_ctor_get(v_e_5275_, 2);
lean_inc_ref(v_body_5283_);
lean_dec_ref_known(v_e_5275_, 3);
v_d_5278_ = v_binderType_5282_;
v_b_5279_ = v_body_5283_;
goto v___jp_5277_;
}
case 6:
{
lean_object* v_binderType_5284_; lean_object* v_body_5285_; 
v_binderType_5284_ = lean_ctor_get(v_e_5275_, 1);
lean_inc_ref(v_binderType_5284_);
v_body_5285_ = lean_ctor_get(v_e_5275_, 2);
lean_inc_ref(v_body_5285_);
lean_dec_ref_known(v_e_5275_, 3);
v_d_5278_ = v_binderType_5284_;
v_b_5279_ = v_body_5285_;
goto v___jp_5277_;
}
case 10:
{
lean_object* v_expr_5286_; 
v_expr_5286_ = lean_ctor_get(v_e_5275_, 1);
lean_inc_ref(v_expr_5286_);
lean_dec_ref_known(v_e_5275_, 2);
v_e_5275_ = v_expr_5286_;
goto _start;
}
case 8:
{
lean_object* v_type_5288_; lean_object* v_value_5289_; lean_object* v_body_5290_; uint8_t v___x_5291_; 
v_type_5288_ = lean_ctor_get(v_e_5275_, 1);
lean_inc_ref(v_type_5288_);
v_value_5289_ = lean_ctor_get(v_e_5275_, 2);
lean_inc_ref(v_value_5289_);
v_body_5290_ = lean_ctor_get(v_e_5275_, 3);
lean_inc_ref(v_body_5290_);
lean_dec_ref_known(v_e_5275_, 4);
v___x_5291_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5274_, v_type_5288_);
if (v___x_5291_ == 0)
{
uint8_t v___x_5292_; 
v___x_5292_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5274_, v_value_5289_);
if (v___x_5292_ == 0)
{
v_e_5275_ = v_body_5290_;
goto _start;
}
else
{
lean_dec_ref(v_body_5290_);
return v___x_5276_;
}
}
else
{
lean_dec_ref(v_body_5290_);
lean_dec_ref(v_value_5289_);
return v___x_5276_;
}
}
case 5:
{
lean_object* v_fn_5294_; lean_object* v_arg_5295_; uint8_t v___x_5296_; 
v_fn_5294_ = lean_ctor_get(v_e_5275_, 0);
lean_inc_ref(v_fn_5294_);
v_arg_5295_ = lean_ctor_get(v_e_5275_, 1);
lean_inc_ref(v_arg_5295_);
lean_dec_ref_known(v_e_5275_, 2);
v___x_5296_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5274_, v_fn_5294_);
if (v___x_5296_ == 0)
{
v_e_5275_ = v_arg_5295_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5295_);
return v___x_5276_;
}
}
case 11:
{
lean_object* v_struct_5298_; 
v_struct_5298_ = lean_ctor_get(v_e_5275_, 2);
lean_inc_ref(v_struct_5298_);
lean_dec_ref_known(v_e_5275_, 3);
v_e_5275_ = v_struct_5298_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v_fvarId_5300_ = lean_ctor_get(v_e_5275_, 0);
lean_inc(v_fvarId_5300_);
lean_dec_ref_known(v_e_5275_, 1);
v___x_5301_ = l_Lean_Expr_fvar___override(v_fvarId_5300_);
v___x_5302_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5274_, v___x_5301_);
lean_dec_ref(v___x_5301_);
return v___x_5302_;
}
default: 
{
uint8_t v___x_5303_; 
lean_dec_ref(v_e_5275_);
v___x_5303_ = 0;
return v___x_5303_;
}
}
}
v___jp_5277_:
{
uint8_t v___x_5280_; 
v___x_5280_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5274_, v_d_5278_);
if (v___x_5280_ == 0)
{
v_e_5275_ = v_b_5279_;
goto _start;
}
else
{
lean_dec_ref(v_b_5279_);
return v___x_5276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5304_, lean_object* v_e_5305_){
_start:
{
uint8_t v_res_5306_; lean_object* v_r_5307_; 
v_res_5306_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5304_, v_e_5305_);
lean_dec_ref(v_xs_5304_);
v_r_5307_ = lean_box(v_res_5306_);
return v_r_5307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5310_ = l_Lean_stringToMessageData(v___x_5309_);
return v___x_5310_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5313_ = l_Lean_stringToMessageData(v___x_5312_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5314_, lean_object* v_type_5315_, lean_object* v_as_5316_, size_t v_sz_5317_, size_t v_i_5318_, lean_object* v_b_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_a_5326_; uint8_t v___x_5330_; 
v___x_5330_ = lean_usize_dec_lt(v_i_5318_, v_sz_5317_);
if (v___x_5330_ == 0)
{
lean_object* v___x_5331_; 
lean_dec_ref(v_type_5315_);
v___x_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5331_, 0, v_b_5319_);
return v___x_5331_;
}
else
{
lean_object* v___x_5332_; lean_object* v_a_5333_; uint8_t v___x_5334_; 
v___x_5332_ = lean_box(0);
v_a_5333_ = lean_array_uget_borrowed(v_as_5316_, v_i_5318_);
lean_inc(v_a_5333_);
v___x_5334_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5314_, v_a_5333_);
if (v___x_5334_ == 0)
{
v_a_5326_ = v___x_5332_;
goto v___jp_5325_;
}
else
{
lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5335_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5333_);
v___x_5336_ = l_Lean_MessageData_ofExpr(v_a_5333_);
v___x_5337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5335_);
lean_ctor_set(v___x_5337_, 1, v___x_5336_);
v___x_5338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5337_);
lean_ctor_set(v___x_5339_, 1, v___x_5338_);
lean_inc_ref(v_type_5315_);
v___x_5340_ = l_Lean_MessageData_ofExpr(v_type_5315_);
v___x_5341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5339_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5341_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_dec_ref_known(v___x_5342_, 1);
v_a_5326_ = v___x_5332_;
goto v___jp_5325_;
}
else
{
lean_dec_ref(v_type_5315_);
return v___x_5342_;
}
}
}
v___jp_5325_:
{
size_t v___x_5327_; size_t v___x_5328_; 
v___x_5327_ = ((size_t)1ULL);
v___x_5328_ = lean_usize_add(v_i_5318_, v___x_5327_);
v_i_5318_ = v___x_5328_;
v_b_5319_ = v_a_5326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5343_, lean_object* v_type_5344_, lean_object* v_as_5345_, lean_object* v_sz_5346_, lean_object* v_i_5347_, lean_object* v_b_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
size_t v_sz_boxed_5354_; size_t v_i_boxed_5355_; lean_object* v_res_5356_; 
v_sz_boxed_5354_ = lean_unbox_usize(v_sz_5346_);
lean_dec(v_sz_5346_);
v_i_boxed_5355_ = lean_unbox_usize(v_i_5347_);
lean_dec(v_i_5347_);
v_res_5356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5343_, v_type_5344_, v_as_5345_, v_sz_boxed_5354_, v_i_boxed_5355_, v_b_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec_ref(v_as_5345_);
lean_dec_ref(v_xs_5343_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5357_, size_t v_i_5358_, lean_object* v_bs_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_usize_dec_lt(v_i_5358_, v_sz_5357_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; 
v___x_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5366_, 0, v_bs_5359_);
return v___x_5366_;
}
else
{
lean_object* v_v_5367_; lean_object* v___x_5368_; 
v_v_5367_ = lean_array_uget_borrowed(v_bs_5359_, v_i_5358_);
lean_inc(v___y_5363_);
lean_inc_ref(v___y_5362_);
lean_inc(v___y_5361_);
lean_inc_ref(v___y_5360_);
lean_inc(v_v_5367_);
v___x_5368_ = lean_infer_type(v_v_5367_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5370_; lean_object* v_bs_x27_5371_; size_t v___x_5372_; size_t v___x_5373_; lean_object* v___x_5374_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
lean_inc(v_a_5369_);
lean_dec_ref_known(v___x_5368_, 1);
v___x_5370_ = lean_unsigned_to_nat(0u);
v_bs_x27_5371_ = lean_array_uset(v_bs_5359_, v_i_5358_, v___x_5370_);
v___x_5372_ = ((size_t)1ULL);
v___x_5373_ = lean_usize_add(v_i_5358_, v___x_5372_);
v___x_5374_ = lean_array_uset(v_bs_x27_5371_, v_i_5358_, v_a_5369_);
v_i_5358_ = v___x_5373_;
v_bs_5359_ = v___x_5374_;
goto _start;
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec_ref(v_bs_5359_);
v_a_5376_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5368_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5368_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5384_, lean_object* v_i_5385_, lean_object* v_bs_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
size_t v_sz_boxed_5392_; size_t v_i_boxed_5393_; lean_object* v_res_5394_; 
v_sz_boxed_5392_ = lean_unbox_usize(v_sz_5384_);
lean_dec(v_sz_5384_);
v_i_boxed_5393_ = lean_unbox_usize(v_i_5385_);
lean_dec(v_i_5385_);
v_res_5394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5392_, v_i_boxed_5393_, v_bs_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
return v_res_5394_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5397_ = l_Lean_stringToMessageData(v___x_5396_);
return v___x_5397_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5400_ = l_Lean_stringToMessageData(v___x_5399_);
return v___x_5400_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5402_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5403_ = l_Lean_stringToMessageData(v___x_5402_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5404_, lean_object* v_n_5405_, lean_object* v_xs_5406_, lean_object* v_x_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v___x_5437_; uint8_t v___x_5438_; 
v___x_5437_ = lean_array_get_size(v_xs_5406_);
v___x_5438_ = lean_nat_dec_eq(v___x_5437_, v_n_5405_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec_ref(v_xs_5406_);
v___x_5439_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5440_ = l_Lean_MessageData_ofExpr(v_type_5404_);
v___x_5441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5439_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5441_);
lean_ctor_set(v___x_5443_, 1, v___x_5442_);
v___x_5444_ = l_Nat_reprFast(v_n_5405_);
v___x_5445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5444_);
v___x_5446_ = l_Lean_MessageData_ofFormat(v___x_5445_);
v___x_5447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5443_);
lean_ctor_set(v___x_5447_, 1, v___x_5446_);
v___x_5448_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5447_);
lean_ctor_set(v___x_5449_, 1, v___x_5448_);
v___x_5450_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5449_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
else
{
lean_dec(v_n_5405_);
goto v___jp_5413_;
}
v___jp_5413_:
{
size_t v_sz_5414_; size_t v___x_5415_; lean_object* v___x_5416_; 
v_sz_5414_ = lean_array_size(v_xs_5406_);
v___x_5415_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5406_);
v___x_5416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5414_, v___x_5415_, v_xs_5406_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v_a_5417_; lean_object* v___x_5418_; size_t v_sz_5419_; lean_object* v___x_5420_; 
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
lean_dec_ref_known(v___x_5416_, 1);
v___x_5418_ = lean_box(0);
v_sz_5419_ = lean_array_size(v_a_5417_);
v___x_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5406_, v_type_5404_, v_a_5417_, v_sz_5419_, v___x_5415_, v___x_5418_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
lean_dec_ref(v_xs_5406_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5427_ == 0)
{
lean_object* v_unused_5428_; 
v_unused_5428_ = lean_ctor_get(v___x_5420_, 0);
lean_dec(v_unused_5428_);
v___x_5422_ = v___x_5420_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_dec(v___x_5420_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v_a_5417_);
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5417_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec(v_a_5417_);
v_a_5429_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5420_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5420_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5406_);
lean_dec_ref(v_type_5404_);
return v___x_5416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5459_, lean_object* v_n_5460_, lean_object* v_xs_5461_, lean_object* v_x_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5459_, v_n_5460_, v_xs_5461_, v_x_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec_ref(v_x_5462_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5469_, lean_object* v_type_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v___f_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; 
lean_inc(v_n_5469_);
lean_inc_ref(v_type_5470_);
v___f_5476_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5476_, 0, v_type_5470_);
lean_closure_set(v___f_5476_, 1, v_n_5469_);
v___x_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5477_, 0, v_n_5469_);
v___x_5478_ = 0;
v___x_5479_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5470_, v___x_5477_, v___f_5476_, v___x_5478_, v___x_5478_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5480_, lean_object* v_type_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Lean_Meta_arrowDomainsN(v_n_5480_, v_type_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec_ref(v_a_5482_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5488_, lean_object* v_e_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_){
_start:
{
lean_object* v___x_5495_; 
lean_inc(v_a_5493_);
lean_inc_ref(v_a_5492_);
lean_inc(v_a_5491_);
lean_inc_ref(v_a_5490_);
v___x_5495_ = lean_infer_type(v_e_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5497_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v___x_5495_, 1);
v___x_5497_ = l_Lean_Meta_arrowDomainsN(v_n_5488_, v_a_5496_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_);
return v___x_5497_;
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
lean_dec(v_n_5488_);
v_a_5498_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5495_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5495_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5506_, lean_object* v_e_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l_Lean_Meta_inferArgumentTypesN(v_n_5506_, v_e_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
lean_dec(v_a_5511_);
lean_dec_ref(v_a_5510_);
lean_dec(v_a_5509_);
lean_dec_ref(v_a_5508_);
return v_res_5513_;
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
