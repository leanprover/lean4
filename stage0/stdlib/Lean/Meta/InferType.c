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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
v___x_998_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_998_, 10, v___x_996_);
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
size_t v_x_1234__boxed_1861_; size_t v_x_1235__boxed_1862_; lean_object* v_res_1863_; 
v_x_1234__boxed_1861_ = lean_unbox_usize(v_x_1857_);
lean_dec(v_x_1857_);
v_x_1235__boxed_1862_ = lean_unbox_usize(v_x_1858_);
lean_dec(v_x_1858_);
v_res_1863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1856_, v_x_1234__boxed_1861_, v_x_1235__boxed_1862_, v_x_1859_, v_x_1860_);
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
lean_object* v___x_1875_; lean_object* v_mctx_1876_; lean_object* v_cache_1877_; lean_object* v_zetaDeltaFVarIds_1878_; lean_object* v_postponed_1879_; lean_object* v_diag_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1909_; 
v___x_1875_ = lean_st_ref_take(v___y_1873_);
v_mctx_1876_ = lean_ctor_get(v___x_1875_, 0);
v_cache_1877_ = lean_ctor_get(v___x_1875_, 1);
v_zetaDeltaFVarIds_1878_ = lean_ctor_get(v___x_1875_, 2);
v_postponed_1879_ = lean_ctor_get(v___x_1875_, 3);
v_diag_1880_ = lean_ctor_get(v___x_1875_, 4);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1882_ = v___x_1875_;
v_isShared_1883_ = v_isSharedCheck_1909_;
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
v_isShared_1883_ = v_isSharedCheck_1909_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_depth_1884_; lean_object* v_levelAssignDepth_1885_; lean_object* v_lmvarCounter_1886_; lean_object* v_mvarCounter_1887_; lean_object* v_lDecls_1888_; lean_object* v_decls_1889_; lean_object* v_userNames_1890_; lean_object* v_lAssignment_1891_; lean_object* v_eAssignment_1892_; lean_object* v_dAssignment_1893_; lean_object* v_instanceTypedMVars_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1908_; 
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
v_instanceTypedMVars_1894_ = lean_ctor_get(v_mctx_1876_, 10);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_mctx_1876_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1896_ = v_mctx_1876_;
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_instanceTypedMVars_1894_);
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
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1892_, v_mvarId_1871_, v_val_1872_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 8, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_depth_1884_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_levelAssignDepth_1885_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_lmvarCounter_1886_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_mvarCounter_1887_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_lDecls_1888_);
lean_ctor_set(v_reuseFailAlloc_1907_, 5, v_decls_1889_);
lean_ctor_set(v_reuseFailAlloc_1907_, 6, v_userNames_1890_);
lean_ctor_set(v_reuseFailAlloc_1907_, 7, v_lAssignment_1891_);
lean_ctor_set(v_reuseFailAlloc_1907_, 8, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 9, v_dAssignment_1893_);
lean_ctor_set(v_reuseFailAlloc_1907_, 10, v_instanceTypedMVars_1894_);
v___x_1900_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1900_);
v___x_1902_ = v___x_1882_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_cache_1877_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_zetaDeltaFVarIds_1878_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_postponed_1879_);
lean_ctor_set(v_reuseFailAlloc_1906_, 4, v_diag_1880_);
v___x_1902_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_st_ref_put(v___y_1873_, v___x_1902_);
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1910_, lean_object* v_val_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1910_, v_val_1911_, v___y_1912_);
lean_dec(v___y_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; 
lean_inc(v_a_1919_);
lean_inc_ref(v_a_1918_);
lean_inc(v_a_1917_);
lean_inc_ref(v_a_1916_);
lean_inc_ref(v_type_1915_);
v___x_1921_ = lean_infer_type(v_type_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l_Lean_Meta_whnfD(v_a_1922_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1958_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1958_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1958_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
switch(lean_obj_tag(v_a_1924_))
{
case 3:
{
lean_object* v_u_1928_; lean_object* v___x_1930_; 
lean_dec_ref(v_type_1915_);
v_u_1928_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_u_1928_);
lean_dec_ref_known(v_a_1924_, 1);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_u_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_u_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
case 2:
{
lean_object* v_mvarId_1932_; lean_object* v___x_1933_; 
lean_del_object(v___x_1926_);
v_mvarId_1932_ = lean_ctor_get(v_a_1924_, 0);
lean_inc_n(v_mvarId_1932_, 2);
lean_dec_ref_known(v_a_1924_, 1);
v___x_1933_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1932_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = lean_unbox(v_a_1934_);
lean_dec(v_a_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v_type_1915_);
v___x_1936_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_n(v_a_1937_, 2);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l_Lean_mkSort(v_a_1937_);
v___x_1939_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1932_, v___x_1938_, v_a_1917_);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1947_);
v___x_1941_ = v___x_1939_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v_a_1937_);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1937_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_dec(v_mvarId_1932_);
return v___x_1936_;
}
}
else
{
lean_object* v___x_1948_; 
lean_dec(v_mvarId_1932_);
v___x_1948_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1948_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_mvarId_1932_);
lean_dec_ref(v_type_1915_);
v_a_1949_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1933_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1933_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
default: 
{
lean_object* v___x_1957_; 
lean_del_object(v___x_1926_);
lean_dec(v_a_1924_);
v___x_1957_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_type_1915_);
v_a_1959_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1923_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1923_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_type_1915_);
v_a_1967_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1921_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1921_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_getLevel(v_type_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1982_, lean_object* v_val_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1982_, v_val_1983_, v___y_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1990_, lean_object* v_val_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1990_, v_val_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1999_, v_x_2000_, v_x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2003_, lean_object* v_x_2004_, size_t v_x_2005_, size_t v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2004_, v_x_2005_, v_x_2006_, v_x_2007_, v_x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
size_t v_x_1587__boxed_2016_; size_t v_x_1588__boxed_2017_; lean_object* v_res_2018_; 
v_x_1587__boxed_2016_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_x_1588__boxed_2017_ = lean_unbox_usize(v_x_2013_);
lean_dec(v_x_2013_);
v_res_2018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2010_, v_x_2011_, v_x_1587__boxed_2016_, v_x_1588__boxed_2017_, v_x_2014_, v_x_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2019_, lean_object* v_n_2020_, lean_object* v_k_2021_, lean_object* v_v_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2020_, v_k_2021_, v_v_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2024_, size_t v_depth_2025_, lean_object* v_keys_2026_, lean_object* v_vals_2027_, lean_object* v_heq_2028_, lean_object* v_i_2029_, lean_object* v_entries_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2025_, v_keys_2026_, v_vals_2027_, v_i_2029_, v_entries_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2032_, lean_object* v_depth_2033_, lean_object* v_keys_2034_, lean_object* v_vals_2035_, lean_object* v_heq_2036_, lean_object* v_i_2037_, lean_object* v_entries_2038_){
_start:
{
size_t v_depth_boxed_2039_; lean_object* v_res_2040_; 
v_depth_boxed_2039_ = lean_unbox_usize(v_depth_2033_);
lean_dec(v_depth_2033_);
v_res_2040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2032_, v_depth_boxed_2039_, v_keys_2034_, v_vals_2035_, v_heq_2036_, v_i_2037_, v_entries_2038_);
lean_dec_ref(v_vals_2035_);
lean_dec_ref(v_keys_2034_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2042_, v_x_2043_, v_x_2044_, v_x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2047_, lean_object* v_b_2048_, lean_object* v_c_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v___y_2053_);
lean_inc_ref(v___y_2052_);
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
v___x_2055_ = lean_apply_7(v_k_2047_, v_b_2048_, v_c_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, lean_box(0));
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2056_, lean_object* v_b_2057_, lean_object* v_c_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2056_, v_b_2057_, v_c_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2065_, lean_object* v_k_2066_, uint8_t v_cleanupAnnotations_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___f_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2073_, 0, v_k_2066_);
v___x_2074_ = 0;
v___x_2075_ = lean_box(0);
v___x_2076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2074_, v___x_2075_, v_type_2065_, v___f_2073_, v_cleanupAnnotations_2067_, v___x_2074_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2093_, lean_object* v_k_2094_, lean_object* v_cleanupAnnotations_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2101_; lean_object* v_res_2102_; 
v_cleanupAnnotations_boxed_2101_ = lean_unbox(v_cleanupAnnotations_2095_);
v_res_2102_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2093_, v_k_2094_, v_cleanupAnnotations_boxed_2101_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2103_, lean_object* v_type_2104_, lean_object* v_k_2105_, uint8_t v_cleanupAnnotations_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2104_, v_k_2105_, v_cleanupAnnotations_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_type_2114_, lean_object* v_k_2115_, lean_object* v_cleanupAnnotations_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2122_; lean_object* v_res_2123_; 
v_cleanupAnnotations_boxed_2122_ = lean_unbox(v_cleanupAnnotations_2116_);
v_res_2123_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2113_, v_type_2114_, v_k_2115_, v_cleanupAnnotations_boxed_2122_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_eq(v_i_2125_, v_stop_2126_);
if (v___x_2133_ == 0)
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_sub(v_i_2125_, v___x_2134_);
v___x_2136_ = lean_array_uget_borrowed(v_as_2124_, v___x_2135_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v___y_2129_);
lean_inc_ref(v___y_2128_);
lean_inc(v___x_2136_);
v___x_2137_ = lean_infer_type(v___x_2136_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_Meta_getLevel(v_a_2138_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_mkLevelIMax_x27(v_a_2140_, v_b_2127_);
v_i_2125_ = v___x_2135_;
v_b_2127_ = v___x_2141_;
goto _start;
}
else
{
lean_dec(v_b_2127_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2139_, 1);
v_i_2125_ = v___x_2135_;
v_b_2127_ = v_a_2143_;
goto _start;
}
else
{
return v___x_2139_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_b_2127_);
v_a_2145_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2137_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2137_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_b_2127_);
return v___x_2153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2154_, lean_object* v_i_2155_, lean_object* v_stop_2156_, lean_object* v_b_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
size_t v_i_boxed_2163_; size_t v_stop_boxed_2164_; lean_object* v_res_2165_; 
v_i_boxed_2163_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_stop_boxed_2164_ = lean_unbox_usize(v_stop_2156_);
lean_dec(v_stop_2156_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2154_, v_i_boxed_2163_, v_stop_boxed_2164_, v_b_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec_ref(v_as_2154_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2166_, lean_object* v_e_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___y_2174_; lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Meta_getLevel(v_e_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
v___x_2195_ = lean_array_get_size(v_xs_2166_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_lt(v___x_2196_, v___x_2195_);
if (v___x_2197_ == 0)
{
lean_dec(v_a_2194_);
v___y_2174_ = v___x_2193_;
goto v___jp_2173_;
}
else
{
size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref_known(v___x_2193_, 1);
v___x_2198_ = lean_usize_of_nat(v___x_2195_);
v___x_2199_ = ((size_t)0ULL);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2166_, v___x_2198_, v___x_2199_, v_a_2194_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
v___y_2174_ = v___x_2200_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2201_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2193_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2193_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
v___jp_2173_:
{
if (lean_obj_tag(v___y_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2184_; 
v_a_2175_ = lean_ctor_get(v___y_2174_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___y_2174_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2177_ = v___y_2174_;
v_isShared_2178_ = v_isSharedCheck_2184_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___y_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2184_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2179_ = l_Lean_Level_normalize(v_a_2175_);
lean_dec(v_a_2175_);
v___x_2180_ = l_Lean_mkSort(v___x_2179_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2180_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_a_2185_ = lean_ctor_get(v___y_2174_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___y_2174_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___y_2174_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___y_2174_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2209_, lean_object* v_e_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2209_, v_e_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v_xs_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___f_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___f_2224_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2225_ = 0;
v___x_2226_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2218_, v___f_2224_, v___x_2225_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2234_, lean_object* v_k_2235_, uint8_t v_cleanupAnnotations_2236_, uint8_t v_preserveNondepLet_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___f_2243_; uint8_t v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___f_2243_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2243_, 0, v_k_2235_);
v___x_2244_ = 1;
v___x_2245_ = 0;
v___x_2246_ = lean_box(0);
v___x_2247_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2234_, v___x_2244_, v___x_2244_, v_preserveNondepLet_2237_, v___x_2245_, v___x_2246_, v___f_2243_, v_cleanupAnnotations_2236_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_a_2256_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2247_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2247_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2264_, lean_object* v_k_2265_, lean_object* v_cleanupAnnotations_2266_, lean_object* v_preserveNondepLet_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2273_; uint8_t v_preserveNondepLet_boxed_2274_; lean_object* v_res_2275_; 
v_cleanupAnnotations_boxed_2273_ = lean_unbox(v_cleanupAnnotations_2266_);
v_preserveNondepLet_boxed_2274_ = lean_unbox(v_preserveNondepLet_2267_);
v_res_2275_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2264_, v_k_2265_, v_cleanupAnnotations_boxed_2273_, v_preserveNondepLet_boxed_2274_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2276_, lean_object* v_e_2277_, lean_object* v_k_2278_, uint8_t v_cleanupAnnotations_2279_, uint8_t v_preserveNondepLet_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2277_, v_k_2278_, v_cleanupAnnotations_2279_, v_preserveNondepLet_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_e_2288_, lean_object* v_k_2289_, lean_object* v_cleanupAnnotations_2290_, lean_object* v_preserveNondepLet_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2297_; uint8_t v_preserveNondepLet_boxed_2298_; lean_object* v_res_2299_; 
v_cleanupAnnotations_boxed_2297_ = lean_unbox(v_cleanupAnnotations_2290_);
v_preserveNondepLet_boxed_2298_ = lean_unbox(v_preserveNondepLet_2291_);
v_res_2299_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2287_, v_e_2288_, v_k_2289_, v_cleanupAnnotations_boxed_2297_, v_preserveNondepLet_boxed_2298_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2300_, lean_object* v_e_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
lean_inc(v___y_2305_);
lean_inc_ref(v___y_2304_);
lean_inc(v___y_2303_);
lean_inc_ref(v___y_2302_);
v___x_2307_ = lean_infer_type(v_e_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; uint8_t v___x_2309_; uint8_t v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2309_ = 0;
v___x_2310_ = 1;
v___x_2311_ = 1;
v___x_2312_ = l_Lean_Meta_mkForallFVars(v_xs_2300_, v_a_2308_, v___x_2309_, v___x_2310_, v___x_2309_, v___x_2311_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2312_;
}
else
{
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2313_, lean_object* v_e_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2313_, v_e_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_xs_2313_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v___f_2328_; uint8_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
v___f_2328_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2329_ = 0;
v___x_2330_ = 1;
v___x_2331_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2322_, v___f_2328_, v___x_2329_, v___x_2330_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
return v_res_2338_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2352_ = l_Lean_MessageData_ofName(v_mvarId_2345_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2355_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2364_, lean_object* v_mvarId_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2372_, lean_object* v_mvarId_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2372_, v_mvarId_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v_mctx_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_st_ref_get(v_a_2382_);
v_mctx_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_mctx_2387_);
lean_dec(v___x_2386_);
v___x_2388_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2387_, v_mvarId_2380_);
lean_dec_ref(v_mctx_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_mvarId_2380_);
v_val_2390_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v___x_2388_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v___x_2388_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_type_2394_; lean_object* v___x_2396_; 
v_type_2394_ = lean_ctor_get(v_val_2390_, 2);
lean_inc_ref(v_type_2394_);
lean_dec(v_val_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 0);
lean_ctor_set(v___x_2392_, 0, v_type_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_type_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_lctx_2411_; lean_object* v___x_2412_; 
v_lctx_2411_ = lean_ctor_get(v_a_2407_, 2);
lean_inc(v_fvarId_2406_);
lean_inc_ref(v_lctx_2411_);
v___x_2412_ = lean_local_ctx_find(v_lctx_2411_, v_fvarId_2406_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2406_, v_a_2408_, v_a_2409_);
return v___x_2413_;
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_fvarId_2406_);
v_val_2414_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = l_Lean_LocalDecl_type(v_val_2414_);
lean_dec(v_val_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_a_2424_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2429_, v_a_2430_, v_a_2432_, v_a_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_instMonadEIO(lean_box(0));
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2445_ = l_StateRefT_x27_instMonad___redArg(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___f_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2450_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2450_, 0, v___x_2449_);
return v___f_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___f_2452_; 
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2452_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2452_, 0, v___x_2451_);
return v___f_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v___f_2453_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2454_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___f_2454_);
lean_ctor_set(v___x_2455_, 1, v___f_2453_);
return v___x_2455_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___f_2457_; 
v___x_2456_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2457_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2457_, 0, v___x_2456_);
return v___f_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___f_2459_; 
v___x_2458_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2459_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2459_, 0, v___x_2458_);
return v___f_2459_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; 
v___f_2460_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2461_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___f_2461_);
lean_ctor_set(v___x_2462_, 1, v___f_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2465_, lean_object* v_inferType_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
uint8_t v_cacheInferType_2510_; 
v_cacheInferType_2510_ = lean_ctor_get_uint8(v_a_2467_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2510_ == 0)
{
lean_dec_ref(v_e_2465_);
goto v___jp_2472_;
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_Expr_hasMVar(v_e_2465_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2465_, v_a_2467_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2613_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2613_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2613_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2559_; lean_object* v_cache_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2608_; 
v___x_2559_ = lean_st_ref_get(v_a_2468_);
v_cache_2560_ = lean_ctor_get(v___x_2559_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; lean_object* v_unused_2612_; 
v_unused_2609_ = lean_ctor_get(v___x_2559_, 4);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v___x_2559_, 3);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v___x_2559_, 2);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2612_);
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2608_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_cache_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2608_;
goto v_resetjp_2561_;
}
v___jp_2517_:
{
lean_object* v___x_2518_; 
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
lean_inc(v_a_2468_);
lean_inc_ref(v_a_2467_);
v___x_2518_ = lean_apply_5(v_inferType_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, lean_box(0));
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; uint8_t v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
v___x_2520_ = l_Lean_Expr_hasMVar(v_a_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2557_; 
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2558_);
v___x_2522_ = v___x_2518_;
v_isShared_2523_ = v_isSharedCheck_2557_;
goto v_resetjp_2521_;
}
else
{
lean_dec(v___x_2518_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2557_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v_cache_2525_; lean_object* v_mctx_2526_; lean_object* v_zetaDeltaFVarIds_2527_; lean_object* v_postponed_2528_; lean_object* v_diag_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2556_; 
v___x_2524_ = lean_st_ref_take(v_a_2468_);
v_cache_2525_ = lean_ctor_get(v___x_2524_, 1);
v_mctx_2526_ = lean_ctor_get(v___x_2524_, 0);
v_zetaDeltaFVarIds_2527_ = lean_ctor_get(v___x_2524_, 2);
v_postponed_2528_ = lean_ctor_get(v___x_2524_, 3);
v_diag_2529_ = lean_ctor_get(v___x_2524_, 4);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2531_ = v___x_2524_;
v_isShared_2532_ = v_isSharedCheck_2556_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_diag_2529_);
lean_inc(v_postponed_2528_);
lean_inc(v_zetaDeltaFVarIds_2527_);
lean_inc(v_cache_2525_);
lean_inc(v_mctx_2526_);
lean_dec(v___x_2524_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2556_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_inferType_2533_; lean_object* v_funInfo_2534_; lean_object* v_synthInstance_2535_; lean_object* v_whnf_2536_; lean_object* v_defEqTrans_2537_; lean_object* v_defEqPerm_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2555_; 
v_inferType_2533_ = lean_ctor_get(v_cache_2525_, 0);
v_funInfo_2534_ = lean_ctor_get(v_cache_2525_, 1);
v_synthInstance_2535_ = lean_ctor_get(v_cache_2525_, 2);
v_whnf_2536_ = lean_ctor_get(v_cache_2525_, 3);
v_defEqTrans_2537_ = lean_ctor_get(v_cache_2525_, 4);
v_defEqPerm_2538_ = lean_ctor_get(v_cache_2525_, 5);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_cache_2525_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2540_ = v_cache_2525_;
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_defEqPerm_2538_);
lean_inc(v_defEqTrans_2537_);
lean_inc(v_whnf_2536_);
lean_inc(v_synthInstance_2535_);
lean_inc(v_funInfo_2534_);
lean_inc(v_inferType_2533_);
lean_dec(v_cache_2525_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___f_2542_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2519_);
v___x_2544_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2542_, v___x_2543_, v_inferType_2533_, v_a_2513_, v_a_2519_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2544_);
v___x_2546_ = v___x_2540_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_funInfo_2534_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_synthInstance_2535_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_whnf_2536_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_defEqTrans_2537_);
lean_ctor_set(v_reuseFailAlloc_2554_, 5, v_defEqPerm_2538_);
v___x_2546_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2546_);
v___x_2548_ = v___x_2531_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_mctx_2526_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_zetaDeltaFVarIds_2527_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_postponed_2528_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_diag_2529_);
v___x_2548_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_st_ref_put(v_a_2468_, v___x_2548_);
if (v_isShared_2523_ == 0)
{
v___x_2551_ = v___x_2522_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2519_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2519_);
lean_dec(v_a_2513_);
return v___x_2518_;
}
}
else
{
lean_dec(v_a_2513_);
return v___x_2518_;
}
}
v_resetjp_2561_:
{
lean_object* v_inferType_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_inferType_2564_ = lean_ctor_get(v_cache_2560_, 0);
lean_inc_ref(v_inferType_2564_);
lean_dec_ref(v_cache_2560_);
v___f_2565_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2566_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2513_);
v___x_2567_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2565_, v___x_2566_, v_inferType_2564_, v_a_2513_);
lean_dec_ref(v_inferType_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; lean_object* v_toApplicative_2569_; lean_object* v_toFunctor_2570_; lean_object* v_toSeq_2571_; lean_object* v_toSeqLeft_2572_; lean_object* v_toSeqRight_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___f_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___x_2583_; 
lean_del_object(v___x_2515_);
v___x_2568_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2569_ = lean_ctor_get(v___x_2568_, 0);
v_toFunctor_2570_ = lean_ctor_get(v_toApplicative_2569_, 0);
v_toSeq_2571_ = lean_ctor_get(v_toApplicative_2569_, 2);
v_toSeqLeft_2572_ = lean_ctor_get(v_toApplicative_2569_, 3);
v_toSeqRight_2573_ = lean_ctor_get(v_toApplicative_2569_, 4);
v___f_2574_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2575_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2570_, 2);
v___f_2576_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2576_, 0, v_toFunctor_2570_);
v___f_2577_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2577_, 0, v_toFunctor_2570_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___f_2576_);
lean_ctor_set(v___x_2578_, 1, v___f_2577_);
lean_inc(v_toSeqRight_2573_);
v___f_2579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2579_, 0, v_toSeqRight_2573_);
lean_inc(v_toSeqLeft_2572_);
v___f_2580_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2580_, 0, v_toSeqLeft_2572_);
lean_inc(v_toSeq_2571_);
v___f_2581_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2581_, 0, v_toSeq_2571_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v___f_2579_);
lean_ctor_set(v___x_2562_, 3, v___f_2580_);
lean_ctor_set(v___x_2562_, 2, v___f_2581_);
lean_ctor_set(v___x_2562_, 1, v___f_2574_);
lean_ctor_set(v___x_2562_, 0, v___x_2578_);
v___x_2583_ = v___x_2562_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___f_2574_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v___f_2581_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v___f_2580_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v___f_2579_);
v___x_2583_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v_cancelTk_x3f_2585_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___f_2575_);
v_cancelTk_x3f_2585_ = lean_ctor_get(v_a_2469_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2585_) == 1)
{
lean_object* v_val_2586_; uint8_t v___x_2587_; 
v_val_2586_ = lean_ctor_get(v_cancelTk_x3f_2585_, 0);
v___x_2587_ = l_IO_CancelToken_isSet(v_val_2586_);
if (v___x_2587_ == 0)
{
lean_dec_ref_known(v___x_2584_, 2);
goto v___jp_2517_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2392__overap_2593_; lean_object* v___x_2594_; 
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2589_ = l_Lean_Core_instMonadRefCoreM;
v___x_2590_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2591_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2590_, v___x_2584_);
v___x_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2588_);
lean_ctor_set(v___x_2592_, 1, v___x_2589_);
lean_ctor_set(v___x_2592_, 2, v___x_2591_);
v___x_2392__overap_2593_ = l_Lean_throwInterruptException___redArg(v___x_2592_);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
v___x_2594_ = lean_apply_3(v___x_2392__overap_2593_, v_a_2469_, v_a_2470_, lean_box(0));
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_dec_ref_known(v___x_2594_, 1);
goto v___jp_2517_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_a_2513_);
lean_dec_ref(v_inferType_2466_);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2584_, 2);
goto v___jp_2517_;
}
}
}
else
{
lean_object* v_val_2604_; lean_object* v___x_2606_; 
lean_del_object(v___x_2562_);
lean_dec(v_a_2513_);
lean_dec_ref(v_inferType_2466_);
v_val_2604_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v___x_2567_, 1);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_val_2604_);
v___x_2606_ = v___x_2515_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_val_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v_inferType_2466_);
v_a_2614_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2512_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2512_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_dec_ref(v_e_2465_);
goto v___jp_2472_;
}
}
v___jp_2472_:
{
lean_object* v___x_2473_; lean_object* v_toApplicative_2474_; lean_object* v_toFunctor_2475_; lean_object* v_toSeq_2476_; lean_object* v_toSeqLeft_2477_; lean_object* v_toSeqRight_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_cancelTk_x3f_2489_; 
v___x_2473_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2474_ = lean_ctor_get(v___x_2473_, 0);
v_toFunctor_2475_ = lean_ctor_get(v_toApplicative_2474_, 0);
v_toSeq_2476_ = lean_ctor_get(v_toApplicative_2474_, 2);
v_toSeqLeft_2477_ = lean_ctor_get(v_toApplicative_2474_, 3);
v_toSeqRight_2478_ = lean_ctor_get(v_toApplicative_2474_, 4);
v___f_2479_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2480_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2475_, 2);
v___f_2481_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2481_, 0, v_toFunctor_2475_);
v___f_2482_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2482_, 0, v_toFunctor_2475_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___f_2481_);
lean_ctor_set(v___x_2483_, 1, v___f_2482_);
lean_inc(v_toSeqRight_2478_);
v___f_2484_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2484_, 0, v_toSeqRight_2478_);
lean_inc(v_toSeqLeft_2477_);
v___f_2485_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2485_, 0, v_toSeqLeft_2477_);
lean_inc(v_toSeq_2476_);
v___f_2486_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2486_, 0, v_toSeq_2476_);
v___x_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2483_);
lean_ctor_set(v___x_2487_, 1, v___f_2479_);
lean_ctor_set(v___x_2487_, 2, v___f_2486_);
lean_ctor_set(v___x_2487_, 3, v___f_2485_);
lean_ctor_set(v___x_2487_, 4, v___f_2484_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___f_2480_);
v_cancelTk_x3f_2489_ = lean_ctor_get(v_a_2469_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2489_) == 1)
{
lean_object* v_val_2490_; uint8_t v___x_2491_; 
v_val_2490_ = lean_ctor_get(v_cancelTk_x3f_2489_, 0);
v___x_2491_ = l_IO_CancelToken_isSet(v_val_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref_known(v___x_2488_, 2);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
lean_inc(v_a_2468_);
lean_inc_ref(v_a_2467_);
v___x_2492_ = lean_apply_5(v_inferType_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, lean_box(0));
return v___x_2492_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2189__overap_2498_; lean_object* v___x_2499_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2494_ = l_Lean_Core_instMonadRefCoreM;
v___x_2495_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2496_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2495_, v___x_2488_);
v___x_2497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2493_);
lean_ctor_set(v___x_2497_, 1, v___x_2494_);
lean_ctor_set(v___x_2497_, 2, v___x_2496_);
v___x_2189__overap_2498_ = l_Lean_throwInterruptException___redArg(v___x_2497_);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
v___x_2499_ = lean_apply_3(v___x_2189__overap_2498_, v_a_2469_, v_a_2470_, lean_box(0));
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2500_; 
lean_dec_ref_known(v___x_2499_, 1);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
lean_inc(v_a_2468_);
lean_inc_ref(v_a_2467_);
v___x_2500_ = lean_apply_5(v_inferType_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, lean_box(0));
return v___x_2500_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v_inferType_2466_);
v_a_2501_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2499_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2499_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
else
{
lean_object* v___x_2509_; 
lean_dec_ref_known(v___x_2488_, 2);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
lean_inc(v_a_2468_);
lean_inc_ref(v_a_2467_);
v___x_2509_ = lean_apply_5(v_inferType_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, lean_box(0));
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2622_, lean_object* v_inferType_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2622_, v_inferType_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; uint8_t v___y_2646_; uint8_t v___y_2647_; uint8_t v___y_2677_; lean_object* v___x_2704_; uint8_t v_transparency_2705_; uint8_t v___x_2706_; uint8_t v___x_2707_; 
v___x_2704_ = l_Lean_Meta_Context_config(v_a_2631_);
v_transparency_2705_ = lean_ctor_get_uint8(v___x_2704_, 9);
lean_dec_ref(v___x_2704_);
v___x_2706_ = 1;
v___x_2707_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
v___y_2677_ = v_transparency_2705_;
goto v___jp_2676_;
}
else
{
v___y_2677_ = v___x_2706_;
goto v___jp_2676_;
}
v___jp_2636_:
{
lean_object* v___x_2648_; uint8_t v_foApprox_2649_; uint8_t v_ctxApprox_2650_; uint8_t v_quasiPatternApprox_2651_; uint8_t v_constApprox_2652_; uint8_t v_isDefEqStuckEx_2653_; uint8_t v_unificationHints_2654_; uint8_t v_proofIrrelevance_2655_; uint8_t v_assignSyntheticOpaque_2656_; uint8_t v_offsetCnstrs_2657_; uint8_t v_transparency_2658_; uint8_t v_univApprox_2659_; uint8_t v_zetaUnused_2660_; uint8_t v_canUnfoldPredicateConfig_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2675_; 
v___x_2648_ = l_Lean_Meta_Context_config(v___y_2641_);
lean_dec_ref(v___y_2641_);
v_foApprox_2649_ = lean_ctor_get_uint8(v___x_2648_, 0);
v_ctxApprox_2650_ = lean_ctor_get_uint8(v___x_2648_, 1);
v_quasiPatternApprox_2651_ = lean_ctor_get_uint8(v___x_2648_, 2);
v_constApprox_2652_ = lean_ctor_get_uint8(v___x_2648_, 3);
v_isDefEqStuckEx_2653_ = lean_ctor_get_uint8(v___x_2648_, 4);
v_unificationHints_2654_ = lean_ctor_get_uint8(v___x_2648_, 5);
v_proofIrrelevance_2655_ = lean_ctor_get_uint8(v___x_2648_, 6);
v_assignSyntheticOpaque_2656_ = lean_ctor_get_uint8(v___x_2648_, 7);
v_offsetCnstrs_2657_ = lean_ctor_get_uint8(v___x_2648_, 8);
v_transparency_2658_ = lean_ctor_get_uint8(v___x_2648_, 9);
v_univApprox_2659_ = lean_ctor_get_uint8(v___x_2648_, 11);
v_zetaUnused_2660_ = lean_ctor_get_uint8(v___x_2648_, 17);
v_canUnfoldPredicateConfig_2661_ = lean_ctor_get_uint8(v___x_2648_, 19);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2663_ = v___x_2648_;
v_isShared_2664_ = v_isSharedCheck_2675_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v___x_2648_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2675_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint8_t v___x_2665_; uint8_t v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2669_; 
v___x_2665_ = 1;
v___x_2666_ = 0;
v___x_2667_ = 2;
if (v_isShared_2664_ == 0)
{
v___x_2669_ = v___x_2663_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 0, v_foApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 1, v_ctxApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 2, v_quasiPatternApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 3, v_constApprox_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 4, v_isDefEqStuckEx_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 5, v_unificationHints_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 6, v_proofIrrelevance_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 7, v_assignSyntheticOpaque_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 8, v_offsetCnstrs_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 9, v_transparency_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 11, v_univApprox_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 17, v_zetaUnused_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2674_, 19, v_canUnfoldPredicateConfig_2661_);
v___x_2669_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
uint64_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_ctor_set_uint8(v___x_2669_, 10, v___x_2666_);
lean_ctor_set_uint8(v___x_2669_, 12, v___x_2665_);
lean_ctor_set_uint8(v___x_2669_, 13, v___x_2665_);
lean_ctor_set_uint8(v___x_2669_, 14, v___x_2667_);
lean_ctor_set_uint8(v___x_2669_, 15, v___x_2665_);
lean_ctor_set_uint8(v___x_2669_, 16, v___x_2665_);
lean_ctor_set_uint8(v___x_2669_, 18, v___x_2665_);
v___x_2670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2669_);
v___x_2671_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set_uint64(v___x_2671_, sizeof(void*)*1, v___x_2670_);
lean_inc(v___y_2637_);
lean_inc(v___y_2642_);
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2639_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2644_);
v___x_2672_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___y_2644_);
lean_ctor_set(v___x_2672_, 2, v___y_2643_);
lean_ctor_set(v___x_2672_, 3, v___y_2639_);
lean_ctor_set(v___x_2672_, 4, v___y_2638_);
lean_ctor_set(v___x_2672_, 5, v___y_2642_);
lean_ctor_set(v___x_2672_, 6, v___y_2637_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7, v___y_2646_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 1, v___y_2645_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 2, v___y_2640_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 3, v___y_2647_);
lean_inc(v_a_2634_);
lean_inc_ref(v_a_2633_);
lean_inc(v_a_2632_);
v___x_2673_ = lean_apply_5(v_x_2630_, v___x_2672_, v_a_2632_, v_a_2633_, v_a_2634_, lean_box(0));
return v___x_2673_;
}
}
}
v___jp_2676_:
{
lean_object* v_keyedConfig_2678_; uint8_t v_trackZetaDelta_2679_; lean_object* v_zetaDeltaSet_2680_; lean_object* v_lctx_2681_; lean_object* v_localInstances_2682_; lean_object* v_defEqCtx_x3f_2683_; lean_object* v_synthPendingDepth_2684_; lean_object* v_customCanUnfoldPredicate_x3f_2685_; uint8_t v_univApprox_2686_; uint8_t v_inTypeClassResolution_2687_; uint8_t v_cacheInferType_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v_beta_2692_; 
v_keyedConfig_2678_ = lean_ctor_get(v_a_2631_, 0);
v_trackZetaDelta_2679_ = lean_ctor_get_uint8(v_a_2631_, sizeof(void*)*7);
v_zetaDeltaSet_2680_ = lean_ctor_get(v_a_2631_, 1);
v_lctx_2681_ = lean_ctor_get(v_a_2631_, 2);
v_localInstances_2682_ = lean_ctor_get(v_a_2631_, 3);
v_defEqCtx_x3f_2683_ = lean_ctor_get(v_a_2631_, 4);
v_synthPendingDepth_2684_ = lean_ctor_get(v_a_2631_, 5);
v_customCanUnfoldPredicate_x3f_2685_ = lean_ctor_get(v_a_2631_, 6);
v_univApprox_2686_ = lean_ctor_get_uint8(v_a_2631_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2687_ = lean_ctor_get_uint8(v_a_2631_, sizeof(void*)*7 + 2);
v_cacheInferType_2688_ = lean_ctor_get_uint8(v_a_2631_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2678_);
v___x_2689_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2677_, v_keyedConfig_2678_);
lean_inc(v_customCanUnfoldPredicate_x3f_2685_);
lean_inc(v_synthPendingDepth_2684_);
lean_inc(v_defEqCtx_x3f_2683_);
lean_inc_ref(v_localInstances_2682_);
lean_inc_ref(v_lctx_2681_);
lean_inc(v_zetaDeltaSet_2680_);
v___x_2690_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_zetaDeltaSet_2680_);
lean_ctor_set(v___x_2690_, 2, v_lctx_2681_);
lean_ctor_set(v___x_2690_, 3, v_localInstances_2682_);
lean_ctor_set(v___x_2690_, 4, v_defEqCtx_x3f_2683_);
lean_ctor_set(v___x_2690_, 5, v_synthPendingDepth_2684_);
lean_ctor_set(v___x_2690_, 6, v_customCanUnfoldPredicate_x3f_2685_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7, v_trackZetaDelta_2679_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 1, v_univApprox_2686_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2687_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7 + 3, v_cacheInferType_2688_);
v___x_2691_ = l_Lean_Meta_Context_config(v___x_2690_);
v_beta_2692_ = lean_ctor_get_uint8(v___x_2691_, 13);
if (v_beta_2692_ == 0)
{
lean_dec_ref(v___x_2691_);
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v_iota_2693_; 
v_iota_2693_ = lean_ctor_get_uint8(v___x_2691_, 12);
if (v_iota_2693_ == 0)
{
lean_dec_ref(v___x_2691_);
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v_zeta_2694_; 
v_zeta_2694_ = lean_ctor_get_uint8(v___x_2691_, 15);
if (v_zeta_2694_ == 0)
{
lean_dec_ref(v___x_2691_);
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v_zetaHave_2695_; 
v_zetaHave_2695_ = lean_ctor_get_uint8(v___x_2691_, 18);
if (v_zetaHave_2695_ == 0)
{
lean_dec_ref(v___x_2691_);
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v_zetaDelta_2696_; 
v_zetaDelta_2696_ = lean_ctor_get_uint8(v___x_2691_, 16);
if (v_zetaDelta_2696_ == 0)
{
lean_dec_ref(v___x_2691_);
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v_etaStruct_2697_; uint8_t v_proj_2698_; uint8_t v___x_2699_; uint8_t v___x_2700_; 
v_etaStruct_2697_ = lean_ctor_get_uint8(v___x_2691_, 10);
v_proj_2698_ = lean_ctor_get_uint8(v___x_2691_, 14);
lean_dec_ref(v___x_2691_);
v___x_2699_ = 2;
v___x_2700_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
uint8_t v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = 0;
v___x_2702_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2697_, v___x_2701_);
if (v___x_2702_ == 0)
{
v___y_2637_ = v_customCanUnfoldPredicate_x3f_2685_;
v___y_2638_ = v_defEqCtx_x3f_2683_;
v___y_2639_ = v_localInstances_2682_;
v___y_2640_ = v_inTypeClassResolution_2687_;
v___y_2641_ = v___x_2690_;
v___y_2642_ = v_synthPendingDepth_2684_;
v___y_2643_ = v_lctx_2681_;
v___y_2644_ = v_zetaDeltaSet_2680_;
v___y_2645_ = v_univApprox_2686_;
v___y_2646_ = v_trackZetaDelta_2679_;
v___y_2647_ = v_cacheInferType_2688_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2703_; 
lean_inc(v_a_2634_);
lean_inc_ref(v_a_2633_);
lean_inc(v_a_2632_);
v___x_2703_ = lean_apply_5(v_x_2630_, v___x_2690_, v_a_2632_, v_a_2633_, v_a_2634_, lean_box(0));
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
lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; uint8_t v___y_2732_; uint8_t v___y_2733_; uint8_t v___y_2763_; lean_object* v___x_2790_; uint8_t v_transparency_2791_; uint8_t v___x_2792_; uint8_t v___x_2793_; 
v___x_2790_ = l_Lean_Meta_Context_config(v_a_2717_);
v_transparency_2791_ = lean_ctor_get_uint8(v___x_2790_, 9);
lean_dec_ref(v___x_2790_);
v___x_2792_ = 1;
v___x_2793_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
v___y_2763_ = v_transparency_2791_;
goto v___jp_2762_;
}
else
{
v___y_2763_ = v___x_2792_;
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
lean_inc(v___y_2723_);
lean_inc(v___y_2728_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2725_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2730_);
v___x_2758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___y_2730_);
lean_ctor_set(v___x_2758_, 2, v___y_2729_);
lean_ctor_set(v___x_2758_, 3, v___y_2725_);
lean_ctor_set(v___x_2758_, 4, v___y_2724_);
lean_ctor_set(v___x_2758_, 5, v___y_2728_);
lean_ctor_set(v___x_2758_, 6, v___y_2723_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7, v___y_2732_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 1, v___y_2731_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 2, v___y_2726_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*7 + 3, v___y_2733_);
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
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v_iota_2779_; 
v_iota_2779_ = lean_ctor_get_uint8(v___x_2777_, 12);
if (v_iota_2779_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v_zeta_2780_; 
v_zeta_2780_ = lean_ctor_get_uint8(v___x_2777_, 15);
if (v_zeta_2780_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v_zetaHave_2781_; 
v_zetaHave_2781_ = lean_ctor_get_uint8(v___x_2777_, 18);
if (v_zetaHave_2781_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v_zetaDelta_2782_; 
v_zetaDelta_2782_ = lean_ctor_get_uint8(v___x_2777_, 16);
if (v_zetaDelta_2782_ == 0)
{
lean_dec_ref(v___x_2777_);
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v_etaStruct_2783_; uint8_t v_proj_2784_; uint8_t v___x_2785_; uint8_t v___x_2786_; 
v_etaStruct_2783_ = lean_ctor_get_uint8(v___x_2777_, 10);
v_proj_2784_ = lean_ctor_get_uint8(v___x_2777_, 14);
lean_dec_ref(v___x_2777_);
v___x_2785_ = 2;
v___x_2786_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
uint8_t v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = 0;
v___x_2788_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2783_, v___x_2787_);
if (v___x_2788_ == 0)
{
v___y_2723_ = v_customCanUnfoldPredicate_x3f_2771_;
v___y_2724_ = v_defEqCtx_x3f_2769_;
v___y_2725_ = v_localInstances_2768_;
v___y_2726_ = v_inTypeClassResolution_2773_;
v___y_2727_ = v___x_2776_;
v___y_2728_ = v_synthPendingDepth_2770_;
v___y_2729_ = v_lctx_2767_;
v___y_2730_ = v_zetaDeltaSet_2766_;
v___y_2731_ = v_univApprox_2772_;
v___y_2732_ = v_trackZetaDelta_2765_;
v___y_2733_ = v_cacheInferType_2774_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2789_; 
lean_inc(v_a_2720_);
lean_inc_ref(v_a_2719_);
lean_inc(v_a_2718_);
v___x_2789_ = lean_apply_5(v_x_2716_, v___x_2776_, v_a_2718_, v_a_2719_, v_a_2720_, lean_box(0));
return v___x_2789_;
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
lean_object* v_ks_2919_; lean_object* v_vs_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2940_; 
v_ks_2919_ = lean_ctor_get(v_x_2861_, 0);
v_vs_2920_ = lean_ctor_get(v_x_2861_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2922_ = v_x_2861_;
v_isShared_2923_ = v_isSharedCheck_2940_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_vs_2920_);
lean_inc(v_ks_2919_);
lean_dec(v_x_2861_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2940_;
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
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_ks_2919_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_vs_2920_);
v___x_2925_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v_newNode_2926_; uint8_t v___y_2928_; size_t v___x_2934_; uint8_t v___x_2935_; 
v_newNode_2926_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2925_, v_x_2864_, v_x_2865_);
v___x_2934_ = ((size_t)7ULL);
v___x_2935_ = lean_usize_dec_le(v___x_2934_, v_x_2863_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2926_);
v___x_2937_ = lean_unsigned_to_nat(4u);
v___x_2938_ = lean_nat_dec_lt(v___x_2936_, v___x_2937_);
lean_dec(v___x_2936_);
v___y_2928_ = v___x_2938_;
goto v___jp_2927_;
}
else
{
v___y_2928_ = v___x_2935_;
goto v___jp_2927_;
}
v___jp_2927_:
{
if (v___y_2928_ == 0)
{
lean_object* v_ks_2929_; lean_object* v_vs_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_ks_2929_ = lean_ctor_get(v_newNode_2926_, 0);
lean_inc_ref(v_ks_2929_);
v_vs_2930_ = lean_ctor_get(v_newNode_2926_, 1);
lean_inc_ref(v_vs_2930_);
lean_dec_ref(v_newNode_2926_);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2863_, v_ks_2929_, v_vs_2930_, v___x_2931_, v___x_2932_);
lean_dec_ref(v_vs_2930_);
lean_dec_ref(v_ks_2929_);
return v___x_2933_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2941_, lean_object* v_keys_2942_, lean_object* v_vals_2943_, lean_object* v_i_2944_, lean_object* v_entries_2945_){
_start:
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = lean_array_get_size(v_keys_2942_);
v___x_2947_ = lean_nat_dec_lt(v_i_2944_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_dec(v_i_2944_);
return v_entries_2945_;
}
else
{
lean_object* v_k_2948_; lean_object* v_expr_2949_; uint64_t v_configKey_2950_; lean_object* v_v_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; size_t v_h_2954_; size_t v___x_2955_; lean_object* v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; size_t v_h_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_k_2948_ = lean_array_fget_borrowed(v_keys_2942_, v_i_2944_);
v_expr_2949_ = lean_ctor_get(v_k_2948_, 0);
v_configKey_2950_ = lean_ctor_get_uint64(v_k_2948_, sizeof(void*)*1);
v_v_2951_ = lean_array_fget_borrowed(v_vals_2943_, v_i_2944_);
v___x_2952_ = l_Lean_Expr_hash(v_expr_2949_);
v___x_2953_ = lean_uint64_mix_hash(v___x_2952_, v_configKey_2950_);
v_h_2954_ = lean_uint64_to_usize(v___x_2953_);
v___x_2955_ = ((size_t)5ULL);
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_sub(v_depth_2941_, v___x_2957_);
v___x_2959_ = lean_usize_mul(v___x_2955_, v___x_2958_);
v_h_2960_ = lean_usize_shift_right(v_h_2954_, v___x_2959_);
v___x_2961_ = lean_nat_add(v_i_2944_, v___x_2956_);
lean_dec(v_i_2944_);
lean_inc(v_v_2951_);
lean_inc(v_k_2948_);
v___x_2962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2945_, v_h_2960_, v_depth_2941_, v_k_2948_, v_v_2951_);
v_i_2944_ = v___x_2961_;
v_entries_2945_ = v___x_2962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2964_, lean_object* v_keys_2965_, lean_object* v_vals_2966_, lean_object* v_i_2967_, lean_object* v_entries_2968_){
_start:
{
size_t v_depth_boxed_2969_; lean_object* v_res_2970_; 
v_depth_boxed_2969_ = lean_unbox_usize(v_depth_2964_);
lean_dec(v_depth_2964_);
v_res_2970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2969_, v_keys_2965_, v_vals_2966_, v_i_2967_, v_entries_2968_);
lean_dec_ref(v_vals_2966_);
lean_dec_ref(v_keys_2965_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2971_, lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
size_t v_x_2762__boxed_2976_; size_t v_x_2763__boxed_2977_; lean_object* v_res_2978_; 
v_x_2762__boxed_2976_ = lean_unbox_usize(v_x_2972_);
lean_dec(v_x_2972_);
v_x_2763__boxed_2977_ = lean_unbox_usize(v_x_2973_);
lean_dec(v_x_2973_);
v_res_2978_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2971_, v_x_2762__boxed_2976_, v_x_2763__boxed_2977_, v_x_2974_, v_x_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v_expr_2982_; uint64_t v_configKey_2983_; uint64_t v___x_2984_; uint64_t v___x_2985_; size_t v___x_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v_expr_2982_ = lean_ctor_get(v_x_2980_, 0);
v_configKey_2983_ = lean_ctor_get_uint64(v_x_2980_, sizeof(void*)*1);
v___x_2984_ = l_Lean_Expr_hash(v_expr_2982_);
v___x_2985_ = lean_uint64_mix_hash(v___x_2984_, v_configKey_2983_);
v___x_2986_ = lean_uint64_to_usize(v___x_2985_);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2979_, v___x_2986_, v___x_2987_, v_x_2980_, v_x_2981_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2989_, lean_object* v_vals_2990_, lean_object* v_i_2991_, lean_object* v_k_2992_){
_start:
{
uint8_t v___y_2994_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_array_get_size(v_keys_2989_);
v___x_3001_ = lean_nat_dec_lt(v_i_2991_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
lean_dec(v_i_2991_);
v___x_3002_ = lean_box(0);
return v___x_3002_;
}
else
{
lean_object* v_expr_3003_; uint64_t v_configKey_3004_; lean_object* v_k_x27_3005_; lean_object* v_expr_3006_; uint64_t v_configKey_3007_; uint8_t v___x_3008_; 
v_expr_3003_ = lean_ctor_get(v_k_2992_, 0);
v_configKey_3004_ = lean_ctor_get_uint64(v_k_2992_, sizeof(void*)*1);
v_k_x27_3005_ = lean_array_fget_borrowed(v_keys_2989_, v_i_2991_);
v_expr_3006_ = lean_ctor_get(v_k_x27_3005_, 0);
v_configKey_3007_ = lean_ctor_get_uint64(v_k_x27_3005_, sizeof(void*)*1);
v___x_3008_ = lean_expr_equal(v_expr_3003_, v_expr_3006_);
if (v___x_3008_ == 0)
{
v___y_2994_ = v___x_3008_;
goto v___jp_2993_;
}
else
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_uint64_dec_eq(v_configKey_3004_, v_configKey_3007_);
v___y_2994_ = v___x_3009_;
goto v___jp_2993_;
}
}
v___jp_2993_:
{
if (v___y_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_nat_add(v_i_2991_, v___x_2995_);
lean_dec(v_i_2991_);
v_i_2991_ = v___x_2996_;
goto _start;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_array_fget_borrowed(v_vals_2990_, v_i_2991_);
lean_dec(v_i_2991_);
lean_inc(v___x_2998_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3010_, lean_object* v_vals_3011_, lean_object* v_i_3012_, lean_object* v_k_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3010_, v_vals_3011_, v_i_3012_, v_k_3013_);
lean_dec_ref(v_k_3013_);
lean_dec_ref(v_vals_3011_);
lean_dec_ref(v_keys_3010_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3015_, size_t v_x_3016_, lean_object* v_x_3017_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 0)
{
lean_object* v_es_3018_; lean_object* v___x_3019_; size_t v___x_3020_; size_t v___x_3021_; lean_object* v_j_3022_; lean_object* v___x_3023_; 
v_es_3018_ = lean_ctor_get(v_x_3015_, 0);
v___x_3019_ = lean_box(2);
v___x_3020_ = ((size_t)31ULL);
v___x_3021_ = lean_usize_land(v_x_3016_, v___x_3020_);
v_j_3022_ = lean_usize_to_nat(v___x_3021_);
v___x_3023_ = lean_array_get_borrowed(v___x_3019_, v_es_3018_, v_j_3022_);
lean_dec(v_j_3022_);
switch(lean_obj_tag(v___x_3023_))
{
case 0:
{
lean_object* v_key_3024_; lean_object* v_val_3025_; uint8_t v___y_3027_; lean_object* v_expr_3030_; uint64_t v_configKey_3031_; lean_object* v_expr_3032_; uint64_t v_configKey_3033_; uint8_t v___x_3034_; 
v_key_3024_ = lean_ctor_get(v___x_3023_, 0);
v_val_3025_ = lean_ctor_get(v___x_3023_, 1);
v_expr_3030_ = lean_ctor_get(v_x_3017_, 0);
v_configKey_3031_ = lean_ctor_get_uint64(v_x_3017_, sizeof(void*)*1);
v_expr_3032_ = lean_ctor_get(v_key_3024_, 0);
v_configKey_3033_ = lean_ctor_get_uint64(v_key_3024_, sizeof(void*)*1);
v___x_3034_ = lean_expr_equal(v_expr_3030_, v_expr_3032_);
if (v___x_3034_ == 0)
{
v___y_3027_ = v___x_3034_;
goto v___jp_3026_;
}
else
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_uint64_dec_eq(v_configKey_3031_, v_configKey_3033_);
v___y_3027_ = v___x_3035_;
goto v___jp_3026_;
}
v___jp_3026_:
{
if (v___y_3027_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_box(0);
return v___x_3028_;
}
else
{
lean_object* v___x_3029_; 
lean_inc(v_val_3025_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_val_3025_);
return v___x_3029_;
}
}
}
case 1:
{
lean_object* v_node_3036_; size_t v___x_3037_; size_t v___x_3038_; 
v_node_3036_ = lean_ctor_get(v___x_3023_, 0);
v___x_3037_ = ((size_t)5ULL);
v___x_3038_ = lean_usize_shift_right(v_x_3016_, v___x_3037_);
v_x_3015_ = v_node_3036_;
v_x_3016_ = v___x_3038_;
goto _start;
}
default: 
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_box(0);
return v___x_3040_;
}
}
}
else
{
lean_object* v_ks_3041_; lean_object* v_vs_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_ks_3041_ = lean_ctor_get(v_x_3015_, 0);
v_vs_3042_ = lean_ctor_get(v_x_3015_, 1);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3041_, v_vs_3042_, v___x_3043_, v_x_3017_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
size_t v_x_2971__boxed_3048_; lean_object* v_res_3049_; 
v_x_2971__boxed_3048_ = lean_unbox_usize(v_x_3046_);
lean_dec(v_x_3046_);
v_res_3049_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3045_, v_x_2971__boxed_3048_, v_x_3047_);
lean_dec_ref(v_x_3047_);
lean_dec_ref(v_x_3045_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v_expr_3052_; uint64_t v_configKey_3053_; uint64_t v___x_3054_; uint64_t v___x_3055_; size_t v___x_3056_; lean_object* v___x_3057_; 
v_expr_3052_ = lean_ctor_get(v_x_3051_, 0);
v_configKey_3053_ = lean_ctor_get_uint64(v_x_3051_, sizeof(void*)*1);
v___x_3054_ = l_Lean_Expr_hash(v_expr_3052_);
v___x_3055_ = lean_uint64_mix_hash(v___x_3054_, v_configKey_3053_);
v___x_3056_ = lean_uint64_to_usize(v___x_3055_);
v___x_3057_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3050_, v___x_3056_, v_x_3051_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3058_, lean_object* v_x_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3058_, v_x_3059_);
lean_dec_ref(v_x_3059_);
lean_dec_ref(v_x_3058_);
return v_res_3060_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
switch(lean_obj_tag(v_e_3064_))
{
case 0:
{
lean_object* v_deBruijnIndex_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_deBruijnIndex_3100_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_deBruijnIndex_3100_);
lean_dec_ref_known(v_e_3064_, 1);
v___x_3101_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3102_ = l_Lean_mkBVar(v_deBruijnIndex_3100_);
v___x_3103_ = l_Lean_MessageData_ofExpr(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3104_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3105_;
}
case 1:
{
lean_object* v_fvarId_3106_; lean_object* v___x_3107_; 
v_fvarId_3106_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_fvarId_3106_);
lean_dec_ref_known(v_e_3064_, 1);
v___x_3107_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3106_, v_a_3065_, v_a_3067_, v_a_3068_);
return v___x_3107_;
}
case 2:
{
lean_object* v_mvarId_3108_; lean_object* v___x_3109_; 
v_mvarId_3108_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_mvarId_3108_);
lean_dec_ref_known(v_e_3064_, 1);
v___x_3109_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3108_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3109_;
}
case 3:
{
lean_object* v_u_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_u_3110_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_u_3110_);
lean_dec_ref_known(v_e_3064_, 1);
v___x_3111_ = l_Lean_Level_succ___override(v_u_3110_);
v___x_3112_ = l_Lean_mkSort(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
case 4:
{
lean_object* v_declName_3114_; lean_object* v_us_3115_; 
v_declName_3114_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_declName_3114_);
v_us_3115_ = lean_ctor_get(v_e_3064_, 1);
lean_inc(v_us_3115_);
if (lean_obj_tag(v_us_3115_) == 0)
{
lean_object* v___x_3131_; 
lean_dec_ref_known(v_e_3064_, 2);
v___x_3131_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3131_;
}
else
{
uint8_t v_cacheInferType_3132_; 
v_cacheInferType_3132_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3132_ == 0)
{
lean_dec_ref_known(v_e_3064_, 2);
goto v___jp_3116_;
}
else
{
uint8_t v___x_3133_; 
v___x_3133_ = l_Lean_Expr_hasMVar(v_e_3064_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3199_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3199_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3199_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3179_; lean_object* v_cache_3180_; lean_object* v_inferType_3181_; lean_object* v___x_3182_; 
v___x_3179_ = lean_st_ref_get(v_a_3066_);
v_cache_3180_ = lean_ctor_get(v___x_3179_, 1);
lean_inc_ref(v_cache_3180_);
lean_dec(v___x_3179_);
v_inferType_3181_ = lean_ctor_get(v_cache_3180_, 0);
lean_inc_ref(v_inferType_3181_);
lean_dec_ref(v_cache_3180_);
v___x_3182_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3181_, v_a_3135_);
lean_dec_ref(v_inferType_3181_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_cancelTk_x3f_3183_; 
lean_del_object(v___x_3137_);
v_cancelTk_x3f_3183_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3183_) == 1)
{
lean_object* v_val_3184_; uint8_t v___x_3185_; 
v_val_3184_ = lean_ctor_get(v_cancelTk_x3f_3183_, 0);
v___x_3185_ = l_IO_CancelToken_isSet(v_val_3184_);
if (v___x_3185_ == 0)
{
goto v___jp_3139_;
}
else
{
lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3135_);
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
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
goto v___jp_3139_;
}
}
else
{
lean_object* v_val_3195_; lean_object* v___x_3197_; 
lean_dec(v_a_3135_);
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v_val_3195_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_val_3195_);
lean_dec_ref_known(v___x_3182_, 1);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_val_3195_);
v___x_3197_ = v___x_3137_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_val_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
v___jp_3139_:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; uint8_t v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
v___x_3142_ = l_Lean_Expr_hasMVar(v_a_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3178_);
v___x_3144_ = v___x_3140_;
v_isShared_3145_ = v_isSharedCheck_3177_;
goto v_resetjp_3143_;
}
else
{
lean_dec(v___x_3140_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3177_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v_cache_3147_; lean_object* v_mctx_3148_; lean_object* v_zetaDeltaFVarIds_3149_; lean_object* v_postponed_3150_; lean_object* v_diag_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3176_; 
v___x_3146_ = lean_st_ref_take(v_a_3066_);
v_cache_3147_ = lean_ctor_get(v___x_3146_, 1);
v_mctx_3148_ = lean_ctor_get(v___x_3146_, 0);
v_zetaDeltaFVarIds_3149_ = lean_ctor_get(v___x_3146_, 2);
v_postponed_3150_ = lean_ctor_get(v___x_3146_, 3);
v_diag_3151_ = lean_ctor_get(v___x_3146_, 4);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3153_ = v___x_3146_;
v_isShared_3154_ = v_isSharedCheck_3176_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_diag_3151_);
lean_inc(v_postponed_3150_);
lean_inc(v_zetaDeltaFVarIds_3149_);
lean_inc(v_cache_3147_);
lean_inc(v_mctx_3148_);
lean_dec(v___x_3146_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3176_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_inferType_3155_; lean_object* v_funInfo_3156_; lean_object* v_synthInstance_3157_; lean_object* v_whnf_3158_; lean_object* v_defEqTrans_3159_; lean_object* v_defEqPerm_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3175_; 
v_inferType_3155_ = lean_ctor_get(v_cache_3147_, 0);
v_funInfo_3156_ = lean_ctor_get(v_cache_3147_, 1);
v_synthInstance_3157_ = lean_ctor_get(v_cache_3147_, 2);
v_whnf_3158_ = lean_ctor_get(v_cache_3147_, 3);
v_defEqTrans_3159_ = lean_ctor_get(v_cache_3147_, 4);
v_defEqPerm_3160_ = lean_ctor_get(v_cache_3147_, 5);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_cache_3147_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3162_ = v_cache_3147_;
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_defEqPerm_3160_);
lean_inc(v_defEqTrans_3159_);
lean_inc(v_whnf_3158_);
lean_inc(v_synthInstance_3157_);
lean_inc(v_funInfo_3156_);
lean_inc(v_inferType_3155_);
lean_dec(v_cache_3147_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3175_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_inc(v_a_3141_);
v___x_3164_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3155_, v_a_3135_, v_a_3141_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3166_ = v___x_3162_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_funInfo_3156_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_synthInstance_3157_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_whnf_3158_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_defEqTrans_3159_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v_defEqPerm_3160_);
v___x_3166_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3166_);
v___x_3168_ = v___x_3153_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_mctx_3148_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_zetaDeltaFVarIds_3149_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_postponed_3150_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_diag_3151_);
v___x_3168_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_st_ref_put(v_a_3066_, v___x_3168_);
if (v_isShared_3145_ == 0)
{
v___x_3171_ = v___x_3144_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3141_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3141_);
lean_dec(v_a_3135_);
return v___x_3140_;
}
}
else
{
lean_dec(v_a_3135_);
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v_a_3200_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3134_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3134_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3064_, 2);
goto v___jp_3116_;
}
}
}
v___jp_3116_:
{
lean_object* v_cancelTk_x3f_3117_; 
v_cancelTk_x3f_3117_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3117_) == 1)
{
lean_object* v_val_3118_; uint8_t v___x_3119_; 
v_val_3118_ = lean_ctor_get(v_cancelTk_x3f_3117_, 0);
v___x_3119_ = l_IO_CancelToken_isSet(v_val_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; 
v___x_3120_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_us_3115_);
lean_dec(v_declName_3114_);
v___x_3121_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3114_, v_us_3115_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3130_;
}
}
}
case 5:
{
lean_object* v_fn_3208_; uint8_t v_cacheInferType_3209_; lean_object* v_nargs_3210_; lean_object* v___x_3211_; lean_object* v_dummy_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_fn_3208_ = lean_ctor_get(v_e_3064_, 0);
v_cacheInferType_3209_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*7 + 3);
v_nargs_3210_ = l_Lean_Expr_getAppNumArgs(v_e_3064_);
v___x_3211_ = l_Lean_Expr_getAppFn(v_fn_3208_);
v_dummy_3212_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3210_);
v___x_3213_ = lean_mk_array(v_nargs_3210_, v_dummy_3212_);
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_sub(v_nargs_3210_, v___x_3214_);
lean_dec(v_nargs_3210_);
lean_inc_ref(v_e_3064_);
v___x_3216_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3064_, v___x_3213_, v___x_3215_);
if (v_cacheInferType_3209_ == 0)
{
lean_dec_ref_known(v_e_3064_, 2);
goto v___jp_3217_;
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = l_Lean_Expr_hasMVar(v_e_3064_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3298_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3298_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3298_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3278_; lean_object* v_cache_3279_; lean_object* v_inferType_3280_; lean_object* v___x_3281_; 
v___x_3278_ = lean_st_ref_get(v_a_3066_);
v_cache_3279_ = lean_ctor_get(v___x_3278_, 1);
lean_inc_ref(v_cache_3279_);
lean_dec(v___x_3278_);
v_inferType_3280_ = lean_ctor_get(v_cache_3279_, 0);
lean_inc_ref(v_inferType_3280_);
lean_dec_ref(v_cache_3279_);
v___x_3281_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3280_, v_a_3234_);
lean_dec_ref(v_inferType_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_cancelTk_x3f_3282_; 
lean_del_object(v___x_3236_);
v_cancelTk_x3f_3282_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3282_) == 1)
{
lean_object* v_val_3283_; uint8_t v___x_3284_; 
v_val_3283_ = lean_ctor_get(v_cancelTk_x3f_3282_, 0);
v___x_3284_ = l_IO_CancelToken_isSet(v_val_3283_);
if (v___x_3284_ == 0)
{
goto v___jp_3238_;
}
else
{
lean_object* v___x_3285_; lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3234_);
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
v___x_3285_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
goto v___jp_3238_;
}
}
else
{
lean_object* v_val_3294_; lean_object* v___x_3296_; 
lean_dec(v_a_3234_);
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
v_val_3294_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___x_3281_, 1);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_val_3294_);
v___x_3296_ = v___x_3236_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_val_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
v___jp_3238_:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec_ref(v___x_3216_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; uint8_t v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
v___x_3241_ = l_Lean_Expr_hasMVar(v_a_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3276_; 
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v___x_3239_, 0);
lean_dec(v_unused_3277_);
v___x_3243_ = v___x_3239_;
v_isShared_3244_ = v_isSharedCheck_3276_;
goto v_resetjp_3242_;
}
else
{
lean_dec(v___x_3239_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3276_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v_cache_3246_; lean_object* v_mctx_3247_; lean_object* v_zetaDeltaFVarIds_3248_; lean_object* v_postponed_3249_; lean_object* v_diag_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3275_; 
v___x_3245_ = lean_st_ref_take(v_a_3066_);
v_cache_3246_ = lean_ctor_get(v___x_3245_, 1);
v_mctx_3247_ = lean_ctor_get(v___x_3245_, 0);
v_zetaDeltaFVarIds_3248_ = lean_ctor_get(v___x_3245_, 2);
v_postponed_3249_ = lean_ctor_get(v___x_3245_, 3);
v_diag_3250_ = lean_ctor_get(v___x_3245_, 4);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3252_ = v___x_3245_;
v_isShared_3253_ = v_isSharedCheck_3275_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_diag_3250_);
lean_inc(v_postponed_3249_);
lean_inc(v_zetaDeltaFVarIds_3248_);
lean_inc(v_cache_3246_);
lean_inc(v_mctx_3247_);
lean_dec(v___x_3245_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3275_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_inferType_3254_; lean_object* v_funInfo_3255_; lean_object* v_synthInstance_3256_; lean_object* v_whnf_3257_; lean_object* v_defEqTrans_3258_; lean_object* v_defEqPerm_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3274_; 
v_inferType_3254_ = lean_ctor_get(v_cache_3246_, 0);
v_funInfo_3255_ = lean_ctor_get(v_cache_3246_, 1);
v_synthInstance_3256_ = lean_ctor_get(v_cache_3246_, 2);
v_whnf_3257_ = lean_ctor_get(v_cache_3246_, 3);
v_defEqTrans_3258_ = lean_ctor_get(v_cache_3246_, 4);
v_defEqPerm_3259_ = lean_ctor_get(v_cache_3246_, 5);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_cache_3246_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3261_ = v_cache_3246_;
v_isShared_3262_ = v_isSharedCheck_3274_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_defEqPerm_3259_);
lean_inc(v_defEqTrans_3258_);
lean_inc(v_whnf_3257_);
lean_inc(v_synthInstance_3256_);
lean_inc(v_funInfo_3255_);
lean_inc(v_inferType_3254_);
lean_dec(v_cache_3246_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3274_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_inc(v_a_3240_);
v___x_3263_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3254_, v_a_3234_, v_a_3240_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3263_);
v___x_3265_ = v___x_3261_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_funInfo_3255_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_synthInstance_3256_);
lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_whnf_3257_);
lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_defEqTrans_3258_);
lean_ctor_set(v_reuseFailAlloc_3273_, 5, v_defEqPerm_3259_);
v___x_3265_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3267_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v___x_3265_);
v___x_3267_ = v___x_3252_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_mctx_3247_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_zetaDeltaFVarIds_3248_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_postponed_3249_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_diag_3250_);
v___x_3267_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = lean_st_ref_put(v_a_3066_, v___x_3267_);
if (v_isShared_3244_ == 0)
{
v___x_3270_ = v___x_3243_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3240_);
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
}
}
}
else
{
lean_dec(v_a_3240_);
lean_dec(v_a_3234_);
return v___x_3239_;
}
}
else
{
lean_dec(v_a_3234_);
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
v_a_3299_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3233_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3233_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3064_, 2);
goto v___jp_3217_;
}
}
v___jp_3217_:
{
lean_object* v_cancelTk_x3f_3218_; 
v_cancelTk_x3f_3218_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3218_) == 1)
{
lean_object* v_val_3219_; uint8_t v___x_3220_; 
v_val_3219_ = lean_ctor_get(v_cancelTk_x3f_3218_, 0);
v___x_3220_ = l_IO_CancelToken_isSet(v_val_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec_ref(v___x_3216_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
v___x_3222_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v___x_3231_; 
v___x_3231_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec_ref(v___x_3216_);
return v___x_3231_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3307_; 
v_cacheInferType_3307_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3307_ == 0)
{
goto v___jp_3085_;
}
else
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Lean_Expr_hasMVar(v_e_3064_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_inc_ref(v_e_3064_);
v___x_3309_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3374_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3374_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3374_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3354_; lean_object* v_cache_3355_; lean_object* v_inferType_3356_; lean_object* v___x_3357_; 
v___x_3354_ = lean_st_ref_get(v_a_3066_);
v_cache_3355_ = lean_ctor_get(v___x_3354_, 1);
lean_inc_ref(v_cache_3355_);
lean_dec(v___x_3354_);
v_inferType_3356_ = lean_ctor_get(v_cache_3355_, 0);
lean_inc_ref(v_inferType_3356_);
lean_dec_ref(v_cache_3355_);
v___x_3357_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3356_, v_a_3310_);
lean_dec_ref(v_inferType_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_cancelTk_x3f_3358_; 
lean_del_object(v___x_3312_);
v_cancelTk_x3f_3358_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3358_) == 1)
{
lean_object* v_val_3359_; uint8_t v___x_3360_; 
v_val_3359_ = lean_ctor_get(v_cancelTk_x3f_3358_, 0);
v___x_3360_ = l_IO_CancelToken_isSet(v_val_3359_);
if (v___x_3360_ == 0)
{
goto v___jp_3314_;
}
else
{
lean_object* v___x_3361_; lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3310_);
lean_dec_ref_known(v_e_3064_, 3);
v___x_3361_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
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
else
{
goto v___jp_3314_;
}
}
else
{
lean_object* v_val_3370_; lean_object* v___x_3372_; 
lean_dec(v_a_3310_);
lean_dec_ref_known(v_e_3064_, 3);
v_val_3370_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v___x_3357_, 1);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_val_3370_);
v___x_3372_ = v___x_3312_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_val_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; uint8_t v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
v___x_3317_ = l_Lean_Expr_hasMVar(v_a_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3352_; 
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v___x_3315_, 0);
lean_dec(v_unused_3353_);
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3352_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3352_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v_cache_3322_; lean_object* v_mctx_3323_; lean_object* v_zetaDeltaFVarIds_3324_; lean_object* v_postponed_3325_; lean_object* v_diag_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3351_; 
v___x_3321_ = lean_st_ref_take(v_a_3066_);
v_cache_3322_ = lean_ctor_get(v___x_3321_, 1);
v_mctx_3323_ = lean_ctor_get(v___x_3321_, 0);
v_zetaDeltaFVarIds_3324_ = lean_ctor_get(v___x_3321_, 2);
v_postponed_3325_ = lean_ctor_get(v___x_3321_, 3);
v_diag_3326_ = lean_ctor_get(v___x_3321_, 4);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3328_ = v___x_3321_;
v_isShared_3329_ = v_isSharedCheck_3351_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_diag_3326_);
lean_inc(v_postponed_3325_);
lean_inc(v_zetaDeltaFVarIds_3324_);
lean_inc(v_cache_3322_);
lean_inc(v_mctx_3323_);
lean_dec(v___x_3321_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3351_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_inferType_3330_; lean_object* v_funInfo_3331_; lean_object* v_synthInstance_3332_; lean_object* v_whnf_3333_; lean_object* v_defEqTrans_3334_; lean_object* v_defEqPerm_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3350_; 
v_inferType_3330_ = lean_ctor_get(v_cache_3322_, 0);
v_funInfo_3331_ = lean_ctor_get(v_cache_3322_, 1);
v_synthInstance_3332_ = lean_ctor_get(v_cache_3322_, 2);
v_whnf_3333_ = lean_ctor_get(v_cache_3322_, 3);
v_defEqTrans_3334_ = lean_ctor_get(v_cache_3322_, 4);
v_defEqPerm_3335_ = lean_ctor_get(v_cache_3322_, 5);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_cache_3322_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3337_ = v_cache_3322_;
v_isShared_3338_ = v_isSharedCheck_3350_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_defEqPerm_3335_);
lean_inc(v_defEqTrans_3334_);
lean_inc(v_whnf_3333_);
lean_inc(v_synthInstance_3332_);
lean_inc(v_funInfo_3331_);
lean_inc(v_inferType_3330_);
lean_dec(v_cache_3322_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3350_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_inc(v_a_3316_);
v___x_3339_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3330_, v_a_3310_, v_a_3316_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3339_);
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_funInfo_3331_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_synthInstance_3332_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_whnf_3333_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_defEqTrans_3334_);
lean_ctor_set(v_reuseFailAlloc_3349_, 5, v_defEqPerm_3335_);
v___x_3341_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3341_);
v___x_3343_ = v___x_3328_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_mctx_3323_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_zetaDeltaFVarIds_3324_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_postponed_3325_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_diag_3326_);
v___x_3343_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = lean_st_ref_put(v_a_3066_, v___x_3343_);
if (v_isShared_3320_ == 0)
{
v___x_3346_ = v___x_3319_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3316_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3316_);
lean_dec(v_a_3310_);
return v___x_3315_;
}
}
else
{
lean_dec(v_a_3310_);
return v___x_3315_;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref_known(v_e_3064_, 3);
v_a_3375_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3309_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3309_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
goto v___jp_3085_;
}
}
}
case 9:
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_a_3383_ = lean_ctor_get(v_e_3064_, 0);
lean_inc_ref(v_a_3383_);
lean_dec_ref_known(v_e_3064_, 1);
v___x_3384_ = l_Lean_Literal_type(v_a_3383_);
lean_dec_ref(v_a_3383_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
case 10:
{
lean_object* v_expr_3386_; 
v_expr_3386_ = lean_ctor_get(v_e_3064_, 1);
lean_inc_ref(v_expr_3386_);
lean_dec_ref_known(v_e_3064_, 2);
v_e_3064_ = v_expr_3386_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3388_; lean_object* v_idx_3389_; lean_object* v_struct_3390_; uint8_t v_cacheInferType_3406_; 
v_typeName_3388_ = lean_ctor_get(v_e_3064_, 0);
lean_inc(v_typeName_3388_);
v_idx_3389_ = lean_ctor_get(v_e_3064_, 1);
lean_inc(v_idx_3389_);
v_struct_3390_ = lean_ctor_get(v_e_3064_, 2);
lean_inc_ref(v_struct_3390_);
v_cacheInferType_3406_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3406_ == 0)
{
lean_dec_ref_known(v_e_3064_, 3);
goto v___jp_3391_;
}
else
{
uint8_t v___x_3407_; 
v___x_3407_ = l_Lean_Expr_hasMVar(v_e_3064_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3473_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3473_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3473_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3453_; lean_object* v_cache_3454_; lean_object* v_inferType_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_st_ref_get(v_a_3066_);
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
lean_object* v_cancelTk_x3f_3457_; 
lean_del_object(v___x_3411_);
v_cancelTk_x3f_3457_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3457_) == 1)
{
lean_object* v_val_3458_; uint8_t v___x_3459_; 
v_val_3458_ = lean_ctor_get(v_cancelTk_x3f_3457_, 0);
v___x_3459_ = l_IO_CancelToken_isSet(v_val_3458_);
if (v___x_3459_ == 0)
{
goto v___jp_3413_;
}
else
{
lean_object* v___x_3460_; lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3409_);
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v___x_3460_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
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
lean_object* v_val_3469_; lean_object* v___x_3471_; 
lean_dec(v_a_3409_);
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v_val_3469_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_val_3469_);
lean_dec_ref_known(v___x_3456_, 1);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v_val_3469_);
v___x_3471_ = v___x_3411_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_val_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
v___jp_3413_:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
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
v___x_3420_ = lean_st_ref_take(v_a_3066_);
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
v___x_3443_ = lean_st_ref_put(v_a_3066_, v___x_3442_);
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
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v_a_3474_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3408_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3408_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3064_, 3);
goto v___jp_3391_;
}
}
v___jp_3391_:
{
lean_object* v_cancelTk_x3f_3392_; 
v_cancelTk_x3f_3392_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3392_) == 1)
{
lean_object* v_val_3393_; uint8_t v___x_3394_; 
v_val_3393_ = lean_ctor_get(v_cancelTk_x3f_3392_, 0);
v___x_3394_ = l_IO_CancelToken_isSet(v_val_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
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
v___x_3405_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3405_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3482_; 
v_cacheInferType_3482_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3482_ == 0)
{
goto v___jp_3070_;
}
else
{
uint8_t v___x_3483_; 
v___x_3483_ = l_Lean_Expr_hasMVar(v_e_3064_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_inc_ref(v_e_3064_);
v___x_3484_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3549_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3549_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3549_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3529_; lean_object* v_cache_3530_; lean_object* v_inferType_3531_; lean_object* v___x_3532_; 
v___x_3529_ = lean_st_ref_get(v_a_3066_);
v_cache_3530_ = lean_ctor_get(v___x_3529_, 1);
lean_inc_ref(v_cache_3530_);
lean_dec(v___x_3529_);
v_inferType_3531_ = lean_ctor_get(v_cache_3530_, 0);
lean_inc_ref(v_inferType_3531_);
lean_dec_ref(v_cache_3530_);
v___x_3532_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3531_, v_a_3485_);
lean_dec_ref(v_inferType_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_cancelTk_x3f_3533_; 
lean_del_object(v___x_3487_);
v_cancelTk_x3f_3533_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3533_) == 1)
{
lean_object* v_val_3534_; uint8_t v___x_3535_; 
v_val_3534_ = lean_ctor_get(v_cancelTk_x3f_3533_, 0);
v___x_3535_ = l_IO_CancelToken_isSet(v_val_3534_);
if (v___x_3535_ == 0)
{
goto v___jp_3489_;
}
else
{
lean_object* v___x_3536_; lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v_a_3485_);
lean_dec_ref(v_e_3064_);
v___x_3536_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
goto v___jp_3489_;
}
}
else
{
lean_object* v_val_3545_; lean_object* v___x_3547_; 
lean_dec(v_a_3485_);
lean_dec_ref(v_e_3064_);
v_val_3545_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v___x_3532_, 1);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_val_3545_);
v___x_3547_ = v___x_3487_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_val_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
v___jp_3489_:
{
lean_object* v___x_3490_; 
v___x_3490_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; uint8_t v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
v___x_3492_ = l_Lean_Expr_hasMVar(v_a_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3527_; 
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v___x_3490_, 0);
lean_dec(v_unused_3528_);
v___x_3494_ = v___x_3490_;
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v___x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3527_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v_cache_3497_; lean_object* v_mctx_3498_; lean_object* v_zetaDeltaFVarIds_3499_; lean_object* v_postponed_3500_; lean_object* v_diag_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3526_; 
v___x_3496_ = lean_st_ref_take(v_a_3066_);
v_cache_3497_ = lean_ctor_get(v___x_3496_, 1);
v_mctx_3498_ = lean_ctor_get(v___x_3496_, 0);
v_zetaDeltaFVarIds_3499_ = lean_ctor_get(v___x_3496_, 2);
v_postponed_3500_ = lean_ctor_get(v___x_3496_, 3);
v_diag_3501_ = lean_ctor_get(v___x_3496_, 4);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3503_ = v___x_3496_;
v_isShared_3504_ = v_isSharedCheck_3526_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_diag_3501_);
lean_inc(v_postponed_3500_);
lean_inc(v_zetaDeltaFVarIds_3499_);
lean_inc(v_cache_3497_);
lean_inc(v_mctx_3498_);
lean_dec(v___x_3496_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3526_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_inferType_3505_; lean_object* v_funInfo_3506_; lean_object* v_synthInstance_3507_; lean_object* v_whnf_3508_; lean_object* v_defEqTrans_3509_; lean_object* v_defEqPerm_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3525_; 
v_inferType_3505_ = lean_ctor_get(v_cache_3497_, 0);
v_funInfo_3506_ = lean_ctor_get(v_cache_3497_, 1);
v_synthInstance_3507_ = lean_ctor_get(v_cache_3497_, 2);
v_whnf_3508_ = lean_ctor_get(v_cache_3497_, 3);
v_defEqTrans_3509_ = lean_ctor_get(v_cache_3497_, 4);
v_defEqPerm_3510_ = lean_ctor_get(v_cache_3497_, 5);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_cache_3497_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3512_ = v_cache_3497_;
v_isShared_3513_ = v_isSharedCheck_3525_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_defEqPerm_3510_);
lean_inc(v_defEqTrans_3509_);
lean_inc(v_whnf_3508_);
lean_inc(v_synthInstance_3507_);
lean_inc(v_funInfo_3506_);
lean_inc(v_inferType_3505_);
lean_dec(v_cache_3497_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3525_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
lean_inc(v_a_3491_);
v___x_3514_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3505_, v_a_3485_, v_a_3491_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_funInfo_3506_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_synthInstance_3507_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_whnf_3508_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_defEqTrans_3509_);
lean_ctor_set(v_reuseFailAlloc_3524_, 5, v_defEqPerm_3510_);
v___x_3516_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v___x_3516_);
v___x_3518_ = v___x_3503_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_mctx_3498_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_zetaDeltaFVarIds_3499_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_postponed_3500_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_diag_3501_);
v___x_3518_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3519_ = lean_st_ref_put(v_a_3066_, v___x_3518_);
if (v_isShared_3495_ == 0)
{
v___x_3521_ = v___x_3494_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3491_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3491_);
lean_dec(v_a_3485_);
return v___x_3490_;
}
}
else
{
lean_dec(v_a_3485_);
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec_ref(v_e_3064_);
v_a_3550_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3484_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3484_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
goto v___jp_3070_;
}
}
}
}
v___jp_3070_:
{
lean_object* v_cancelTk_x3f_3071_; 
v_cancelTk_x3f_3071_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3071_) == 1)
{
lean_object* v_val_3072_; uint8_t v___x_3073_; 
v_val_3072_ = lean_ctor_get(v_cancelTk_x3f_3071_, 0);
v___x_3073_ = l_IO_CancelToken_isSet(v_val_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v_e_3064_);
v___x_3075_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3084_;
}
}
v___jp_3085_:
{
lean_object* v_cancelTk_x3f_3086_; 
v_cancelTk_x3f_3086_ = lean_ctor_get(v_a_3067_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3086_) == 1)
{
lean_object* v_val_3087_; uint8_t v___x_3088_; 
v_val_3087_ = lean_ctor_get(v_cancelTk_x3f_3086_, 0);
v___x_3088_ = l_IO_CancelToken_isSet(v_val_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref(v_e_3064_);
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
v___x_3099_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3566_, v_x_3567_, v_x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3571_, v_x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3574_, v_x_3575_, v_x_3576_);
lean_dec_ref(v_x_3576_);
lean_dec_ref(v_x_3575_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3578_, lean_object* v_x_3579_, size_t v_x_3580_, size_t v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_, v_x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
size_t v_x_4009__boxed_3591_; size_t v_x_4010__boxed_3592_; lean_object* v_res_3593_; 
v_x_4009__boxed_3591_ = lean_unbox_usize(v_x_3587_);
lean_dec(v_x_3587_);
v_x_4010__boxed_3592_ = lean_unbox_usize(v_x_3588_);
lean_dec(v_x_3588_);
v_res_3593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3585_, v_x_3586_, v_x_4009__boxed_3591_, v_x_4010__boxed_3592_, v_x_3589_, v_x_3590_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3594_, lean_object* v_x_3595_, size_t v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3595_, v_x_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
size_t v_x_4026__boxed_3603_; lean_object* v_res_3604_; 
v_x_4026__boxed_3603_ = lean_unbox_usize(v_x_3601_);
lean_dec(v_x_3601_);
v_res_3604_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3599_, v_x_3600_, v_x_4026__boxed_3603_, v_x_3602_);
lean_dec_ref(v_x_3602_);
lean_dec_ref(v_x_3600_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3605_, lean_object* v_n_3606_, lean_object* v_k_3607_, lean_object* v_v_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3606_, v_k_3607_, v_v_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3610_, size_t v_depth_3611_, lean_object* v_keys_3612_, lean_object* v_vals_3613_, lean_object* v_heq_3614_, lean_object* v_i_3615_, lean_object* v_entries_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3611_, v_keys_3612_, v_vals_3613_, v_i_3615_, v_entries_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3618_, lean_object* v_depth_3619_, lean_object* v_keys_3620_, lean_object* v_vals_3621_, lean_object* v_heq_3622_, lean_object* v_i_3623_, lean_object* v_entries_3624_){
_start:
{
size_t v_depth_boxed_3625_; lean_object* v_res_3626_; 
v_depth_boxed_3625_ = lean_unbox_usize(v_depth_3619_);
lean_dec(v_depth_3619_);
v_res_3626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3618_, v_depth_boxed_3625_, v_keys_3620_, v_vals_3621_, v_heq_3622_, v_i_3623_, v_entries_3624_);
lean_dec_ref(v_vals_3621_);
lean_dec_ref(v_keys_3620_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3627_, lean_object* v_keys_3628_, lean_object* v_vals_3629_, lean_object* v_heq_3630_, lean_object* v_i_3631_, lean_object* v_k_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3628_, v_vals_3629_, v_i_3631_, v_k_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3634_, lean_object* v_keys_3635_, lean_object* v_vals_3636_, lean_object* v_heq_3637_, lean_object* v_i_3638_, lean_object* v_k_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3634_, v_keys_3635_, v_vals_3636_, v_heq_3637_, v_i_3638_, v_k_3639_);
lean_dec_ref(v_k_3639_);
lean_dec_ref(v_vals_3636_);
lean_dec_ref(v_keys_3635_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3642_, v_x_3643_, v_x_3644_, v_x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = l_Lean_maxRecDepthErrorMessage;
v___x_3653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3655_ = l_Lean_MessageData_ofFormat(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3657_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3658_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v___x_3656_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v_ref_3659_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3667_, lean_object* v_ref_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3668_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_ref_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3675_, v_ref_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___y_3690_; uint8_t v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; uint8_t v___y_3697_; uint8_t v___y_3698_; lean_object* v___y_3699_; uint8_t v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3731_; uint8_t v___y_3732_; lean_object* v_fileName_3765_; lean_object* v_fileMap_3766_; lean_object* v_options_3767_; lean_object* v_currRecDepth_3768_; lean_object* v_maxRecDepth_3769_; lean_object* v_ref_3770_; lean_object* v_currNamespace_3771_; lean_object* v_openDecls_3772_; lean_object* v_initHeartbeats_3773_; lean_object* v_maxHeartbeats_3774_; lean_object* v_quotContext_3775_; lean_object* v_currMacroScope_3776_; uint8_t v_diag_3777_; lean_object* v_cancelTk_x3f_3778_; uint8_t v_suppressElabErrors_3779_; lean_object* v_inheritedTraceOptions_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3798_; 
v_fileName_3765_ = lean_ctor_get(v_a_3686_, 0);
v_fileMap_3766_ = lean_ctor_get(v_a_3686_, 1);
v_options_3767_ = lean_ctor_get(v_a_3686_, 2);
v_currRecDepth_3768_ = lean_ctor_get(v_a_3686_, 3);
v_maxRecDepth_3769_ = lean_ctor_get(v_a_3686_, 4);
v_ref_3770_ = lean_ctor_get(v_a_3686_, 5);
v_currNamespace_3771_ = lean_ctor_get(v_a_3686_, 6);
v_openDecls_3772_ = lean_ctor_get(v_a_3686_, 7);
v_initHeartbeats_3773_ = lean_ctor_get(v_a_3686_, 8);
v_maxHeartbeats_3774_ = lean_ctor_get(v_a_3686_, 9);
v_quotContext_3775_ = lean_ctor_get(v_a_3686_, 10);
v_currMacroScope_3776_ = lean_ctor_get(v_a_3686_, 11);
v_diag_3777_ = lean_ctor_get_uint8(v_a_3686_, sizeof(void*)*14);
v_cancelTk_x3f_3778_ = lean_ctor_get(v_a_3686_, 12);
v_suppressElabErrors_3779_ = lean_ctor_get_uint8(v_a_3686_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3780_ = lean_ctor_get(v_a_3686_, 13);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3686_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3782_ = v_a_3686_;
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
lean_dec(v_a_3686_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3798_;
goto v_resetjp_3781_;
}
v___jp_3689_:
{
lean_object* v___x_3702_; uint8_t v_foApprox_3703_; uint8_t v_ctxApprox_3704_; uint8_t v_quasiPatternApprox_3705_; uint8_t v_constApprox_3706_; uint8_t v_isDefEqStuckEx_3707_; uint8_t v_unificationHints_3708_; uint8_t v_proofIrrelevance_3709_; uint8_t v_assignSyntheticOpaque_3710_; uint8_t v_offsetCnstrs_3711_; uint8_t v_transparency_3712_; uint8_t v_univApprox_3713_; uint8_t v_zetaUnused_3714_; uint8_t v_canUnfoldPredicateConfig_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3729_; 
v___x_3702_ = l_Lean_Meta_Context_config(v___y_3694_);
lean_dec_ref(v___y_3694_);
v_foApprox_3703_ = lean_ctor_get_uint8(v___x_3702_, 0);
v_ctxApprox_3704_ = lean_ctor_get_uint8(v___x_3702_, 1);
v_quasiPatternApprox_3705_ = lean_ctor_get_uint8(v___x_3702_, 2);
v_constApprox_3706_ = lean_ctor_get_uint8(v___x_3702_, 3);
v_isDefEqStuckEx_3707_ = lean_ctor_get_uint8(v___x_3702_, 4);
v_unificationHints_3708_ = lean_ctor_get_uint8(v___x_3702_, 5);
v_proofIrrelevance_3709_ = lean_ctor_get_uint8(v___x_3702_, 6);
v_assignSyntheticOpaque_3710_ = lean_ctor_get_uint8(v___x_3702_, 7);
v_offsetCnstrs_3711_ = lean_ctor_get_uint8(v___x_3702_, 8);
v_transparency_3712_ = lean_ctor_get_uint8(v___x_3702_, 9);
v_univApprox_3713_ = lean_ctor_get_uint8(v___x_3702_, 11);
v_zetaUnused_3714_ = lean_ctor_get_uint8(v___x_3702_, 17);
v_canUnfoldPredicateConfig_3715_ = lean_ctor_get_uint8(v___x_3702_, 19);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3717_ = v___x_3702_;
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v___x_3702_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
uint8_t v___x_3719_; uint8_t v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3723_; 
v___x_3719_ = 1;
v___x_3720_ = 0;
v___x_3721_ = 2;
if (v_isShared_3718_ == 0)
{
v___x_3723_ = v___x_3717_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 0, v_foApprox_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 1, v_ctxApprox_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 2, v_quasiPatternApprox_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 3, v_constApprox_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 4, v_isDefEqStuckEx_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 5, v_unificationHints_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 6, v_proofIrrelevance_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 7, v_assignSyntheticOpaque_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 8, v_offsetCnstrs_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 9, v_transparency_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 11, v_univApprox_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 17, v_zetaUnused_3714_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 19, v_canUnfoldPredicateConfig_3715_);
v___x_3723_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
uint64_t v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
lean_ctor_set_uint8(v___x_3723_, 10, v___x_3720_);
lean_ctor_set_uint8(v___x_3723_, 12, v___x_3719_);
lean_ctor_set_uint8(v___x_3723_, 13, v___x_3719_);
lean_ctor_set_uint8(v___x_3723_, 14, v___x_3721_);
lean_ctor_set_uint8(v___x_3723_, 15, v___x_3719_);
lean_ctor_set_uint8(v___x_3723_, 16, v___x_3719_);
lean_ctor_set_uint8(v___x_3723_, 18, v___x_3719_);
v___x_3724_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3723_);
v___x_3725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set_uint64(v___x_3725_, sizeof(void*)*1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___y_3699_);
lean_ctor_set(v___x_3726_, 2, v___y_3692_);
lean_ctor_set(v___x_3726_, 3, v___y_3696_);
lean_ctor_set(v___x_3726_, 4, v___y_3701_);
lean_ctor_set(v___x_3726_, 5, v___y_3695_);
lean_ctor_set(v___x_3726_, 6, v___y_3693_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*7, v___y_3691_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*7 + 1, v___y_3700_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*7 + 2, v___y_3697_);
lean_ctor_set_uint8(v___x_3726_, sizeof(void*)*7 + 3, v___y_3698_);
v___x_3727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3683_, v___x_3726_, v_a_3685_, v___y_3690_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v___y_3690_);
lean_dec(v_a_3685_);
lean_dec_ref_known(v___x_3726_, 7);
return v___x_3727_;
}
}
}
v___jp_3730_:
{
lean_object* v_keyedConfig_3733_; uint8_t v_trackZetaDelta_3734_; lean_object* v_zetaDeltaSet_3735_; lean_object* v_lctx_3736_; lean_object* v_localInstances_3737_; lean_object* v_defEqCtx_x3f_3738_; lean_object* v_synthPendingDepth_3739_; lean_object* v_customCanUnfoldPredicate_x3f_3740_; uint8_t v_univApprox_3741_; uint8_t v_inTypeClassResolution_3742_; uint8_t v_cacheInferType_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3764_; 
v_keyedConfig_3733_ = lean_ctor_get(v_a_3684_, 0);
v_trackZetaDelta_3734_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*7);
v_zetaDeltaSet_3735_ = lean_ctor_get(v_a_3684_, 1);
v_lctx_3736_ = lean_ctor_get(v_a_3684_, 2);
v_localInstances_3737_ = lean_ctor_get(v_a_3684_, 3);
v_defEqCtx_x3f_3738_ = lean_ctor_get(v_a_3684_, 4);
v_synthPendingDepth_3739_ = lean_ctor_get(v_a_3684_, 5);
v_customCanUnfoldPredicate_x3f_3740_ = lean_ctor_get(v_a_3684_, 6);
v_univApprox_3741_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3742_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*7 + 2);
v_cacheInferType_3743_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*7 + 3);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_a_3684_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3745_ = v_a_3684_;
v_isShared_3746_ = v_isSharedCheck_3764_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3740_);
lean_inc(v_synthPendingDepth_3739_);
lean_inc(v_defEqCtx_x3f_3738_);
lean_inc(v_localInstances_3737_);
lean_inc(v_lctx_3736_);
lean_inc(v_zetaDeltaSet_3735_);
lean_inc(v_keyedConfig_3733_);
lean_dec(v_a_3684_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3764_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_3732_, v_keyedConfig_3733_);
lean_inc(v_customCanUnfoldPredicate_x3f_3740_);
lean_inc(v_synthPendingDepth_3739_);
lean_inc(v_defEqCtx_x3f_3738_);
lean_inc_ref(v_localInstances_3737_);
lean_inc_ref(v_lctx_3736_);
lean_inc(v_zetaDeltaSet_3735_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3747_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_zetaDeltaSet_3735_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_lctx_3736_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_localInstances_3737_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_defEqCtx_x3f_3738_);
lean_ctor_set(v_reuseFailAlloc_3763_, 5, v_synthPendingDepth_3739_);
lean_ctor_set(v_reuseFailAlloc_3763_, 6, v_customCanUnfoldPredicate_x3f_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7, v_trackZetaDelta_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 1, v_univApprox_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3763_, sizeof(void*)*7 + 3, v_cacheInferType_3743_);
v___x_3749_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; uint8_t v_beta_3751_; 
v___x_3750_ = l_Lean_Meta_Context_config(v___x_3749_);
v_beta_3751_ = lean_ctor_get_uint8(v___x_3750_, 13);
if (v_beta_3751_ == 0)
{
lean_dec_ref(v___x_3750_);
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v_iota_3752_; 
v_iota_3752_ = lean_ctor_get_uint8(v___x_3750_, 12);
if (v_iota_3752_ == 0)
{
lean_dec_ref(v___x_3750_);
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v_zeta_3753_; 
v_zeta_3753_ = lean_ctor_get_uint8(v___x_3750_, 15);
if (v_zeta_3753_ == 0)
{
lean_dec_ref(v___x_3750_);
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v_zetaHave_3754_; 
v_zetaHave_3754_ = lean_ctor_get_uint8(v___x_3750_, 18);
if (v_zetaHave_3754_ == 0)
{
lean_dec_ref(v___x_3750_);
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v_zetaDelta_3755_; 
v_zetaDelta_3755_ = lean_ctor_get_uint8(v___x_3750_, 16);
if (v_zetaDelta_3755_ == 0)
{
lean_dec_ref(v___x_3750_);
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v_etaStruct_3756_; uint8_t v_proj_3757_; uint8_t v___x_3758_; uint8_t v___x_3759_; 
v_etaStruct_3756_ = lean_ctor_get_uint8(v___x_3750_, 10);
v_proj_3757_ = lean_ctor_get_uint8(v___x_3750_, 14);
lean_dec_ref(v___x_3750_);
v___x_3758_ = 2;
v___x_3759_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
uint8_t v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = 0;
v___x_3761_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3756_, v___x_3760_);
if (v___x_3761_ == 0)
{
v___y_3690_ = v___y_3731_;
v___y_3691_ = v_trackZetaDelta_3734_;
v___y_3692_ = v_lctx_3736_;
v___y_3693_ = v_customCanUnfoldPredicate_x3f_3740_;
v___y_3694_ = v___x_3749_;
v___y_3695_ = v_synthPendingDepth_3739_;
v___y_3696_ = v_localInstances_3737_;
v___y_3697_ = v_inTypeClassResolution_3742_;
v___y_3698_ = v_cacheInferType_3743_;
v___y_3699_ = v_zetaDeltaSet_3735_;
v___y_3700_ = v_univApprox_3741_;
v___y_3701_ = v_defEqCtx_x3f_3738_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3762_; 
lean_dec(v_customCanUnfoldPredicate_x3f_3740_);
lean_dec(v_synthPendingDepth_3739_);
lean_dec(v_defEqCtx_x3f_3738_);
lean_dec_ref(v_localInstances_3737_);
lean_dec_ref(v_lctx_3736_);
lean_dec(v_zetaDeltaSet_3735_);
v___x_3762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3683_, v___x_3749_, v_a_3685_, v___y_3731_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v___y_3731_);
lean_dec(v_a_3685_);
lean_dec_ref(v___x_3749_);
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
lean_dec(v_a_3687_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec_ref(v_e_3683_);
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
v___x_3785_ = l_Lean_Meta_Context_config(v_a_3684_);
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
v___y_3731_ = v___x_3790_;
v___y_3732_ = v_transparency_3786_;
goto v___jp_3730_;
}
else
{
v___y_3731_ = v___x_3790_;
v___y_3732_ = v___x_3791_;
goto v___jp_3730_;
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
