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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_nbuckets_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = lean_array_get_size(v_data_69_);
v___x_71_ = lean_unsigned_to_nat(2u);
v_nbuckets_72_ = lean_nat_mul(v___x_70_, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_box(0);
v___x_75_ = lean_mk_array(v_nbuckets_72_, v___x_74_);
v___x_76_ = lean_array_propagate_mark(v_data_69_, v___x_75_);
v___x_77_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v___x_73_, v_data_69_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object* v_a_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
else
{
lean_object* v_key_81_; lean_object* v_tail_82_; uint8_t v___y_84_; lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v_fst_88_; lean_object* v_snd_89_; uint8_t v___x_90_; 
v_key_81_ = lean_ctor_get(v_x_79_, 0);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v_fst_86_ = lean_ctor_get(v_key_81_, 0);
v_snd_87_ = lean_ctor_get(v_key_81_, 1);
v_fst_88_ = lean_ctor_get(v_a_78_, 0);
v_snd_89_ = lean_ctor_get(v_a_78_, 1);
v___x_90_ = l_Lean_ExprStructEq_beq(v_fst_86_, v_fst_88_);
if (v___x_90_ == 0)
{
v___y_84_ = v___x_90_;
goto v___jp_83_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = lean_nat_dec_eq(v_snd_87_, v_snd_89_);
v___y_84_ = v___x_91_;
goto v___jp_83_;
}
v___jp_83_:
{
if (v___y_84_ == 0)
{
v_x_79_ = v_tail_82_;
goto _start;
}
else
{
return v___y_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_92_, v_x_93_);
lean_dec(v_x_93_);
lean_dec_ref(v_a_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(lean_object* v_a_96_, lean_object* v_b_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_dec(v_b_97_);
lean_dec_ref(v_a_96_);
return v_x_98_;
}
else
{
lean_object* v_key_99_; lean_object* v_value_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_120_; 
v_key_99_ = lean_ctor_get(v_x_98_, 0);
v_value_100_ = lean_ctor_get(v_x_98_, 1);
v_tail_101_ = lean_ctor_get(v_x_98_, 2);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_120_ == 0)
{
v___x_103_ = v_x_98_;
v_isShared_104_ = v_isSharedCheck_120_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_value_100_);
lean_inc(v_key_99_);
lean_dec(v_x_98_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_120_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___y_106_; lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v_fst_116_; lean_object* v_snd_117_; uint8_t v___x_118_; 
v_fst_114_ = lean_ctor_get(v_key_99_, 0);
v_snd_115_ = lean_ctor_get(v_key_99_, 1);
v_fst_116_ = lean_ctor_get(v_a_96_, 0);
v_snd_117_ = lean_ctor_get(v_a_96_, 1);
v___x_118_ = l_Lean_ExprStructEq_beq(v_fst_114_, v_fst_116_);
if (v___x_118_ == 0)
{
v___y_106_ = v___x_118_;
goto v___jp_105_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_eq(v_snd_115_, v_snd_117_);
v___y_106_ = v___x_119_;
goto v___jp_105_;
}
v___jp_105_:
{
if (v___y_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_96_, v_b_97_, v_tail_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 2, v___x_107_);
v___x_109_ = v___x_103_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_key_99_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_value_100_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v_value_100_);
lean_dec(v_key_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_b_97_);
lean_ctor_set(v___x_103_, 0, v_a_96_);
v___x_112_ = v___x_103_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_96_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_b_97_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_tail_101_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object* v_m_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v_size_124_; lean_object* v_buckets_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_172_; 
v_size_124_ = lean_ctor_get(v_m_121_, 0);
v_buckets_125_ = lean_ctor_get(v_m_121_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_121_);
if (v_isSharedCheck_172_ == 0)
{
v___x_127_ = v_m_121_;
v_isShared_128_ = v_isSharedCheck_172_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_buckets_125_);
lean_inc(v_size_124_);
lean_dec(v_m_121_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_172_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_fst_129_; lean_object* v_snd_130_; lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v_fold_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_bkt_146_; uint8_t v___x_147_; 
v_fst_129_ = lean_ctor_get(v_a_122_, 0);
v_snd_130_ = lean_ctor_get(v_a_122_, 1);
v___x_131_ = lean_array_get_size(v_buckets_125_);
v___x_132_ = l_Lean_ExprStructEq_hash(v_fst_129_);
v___x_133_ = lean_uint64_of_nat(v_snd_130_);
v___x_134_ = lean_uint64_mix_hash(v___x_132_, v___x_133_);
v___x_135_ = 32ULL;
v___x_136_ = lean_uint64_shift_right(v___x_134_, v___x_135_);
v_fold_137_ = lean_uint64_xor(v___x_134_, v___x_136_);
v___x_138_ = 16ULL;
v___x_139_ = lean_uint64_shift_right(v_fold_137_, v___x_138_);
v___x_140_ = lean_uint64_xor(v_fold_137_, v___x_139_);
v___x_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = lean_usize_of_nat(v___x_131_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_sub(v___x_142_, v___x_143_);
v___x_145_ = lean_usize_land(v___x_141_, v___x_144_);
v_bkt_146_ = lean_array_uget_borrowed(v_buckets_125_, v___x_145_);
v___x_147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_122_, v_bkt_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_size_x27_149_; lean_object* v___x_150_; lean_object* v_buckets_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v_size_x27_149_ = lean_nat_add(v_size_124_, v___x_148_);
lean_dec(v_size_124_);
lean_inc(v_bkt_146_);
v___x_150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_150_, 0, v_a_122_);
lean_ctor_set(v___x_150_, 1, v_b_123_);
lean_ctor_set(v___x_150_, 2, v_bkt_146_);
v_buckets_x27_151_ = lean_array_uset(v_buckets_125_, v___x_145_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(4u);
v___x_153_ = lean_nat_mul(v_size_x27_149_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(3u);
v___x_155_ = lean_nat_div(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_array_get_size(v_buckets_x27_151_);
v___x_157_ = lean_nat_dec_le(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v_val_158_; lean_object* v___x_160_; 
v_val_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_buckets_x27_151_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_val_158_);
lean_ctor_set(v___x_127_, 0, v_size_x27_149_);
v___x_160_ = v___x_127_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_val_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_buckets_x27_151_);
lean_ctor_set(v___x_127_, 0, v_size_x27_149_);
v___x_163_ = v___x_127_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_buckets_x27_151_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v___x_165_; lean_object* v_buckets_x27_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_bkt_146_);
v___x_165_ = lean_box(0);
v_buckets_x27_166_ = lean_array_uset(v_buckets_125_, v___x_145_, v___x_165_);
v___x_167_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_122_, v_b_123_, v_bkt_146_);
v___x_168_ = lean_array_uset(v_buckets_x27_166_, v___x_145_, v___x_167_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_168_);
v___x_170_ = v___x_127_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_124_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(lean_object* v_msg_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lean_instInhabitedExpr;
v___x_175_ = lean_panic_fn_borrowed(v___x_174_, v_msg_173_);
return v___x_175_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1(void){
_start:
{
lean_object* v___x_177_; lean_object* v___f_178_; 
v___x_177_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_178_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_178_, 0, v___x_177_);
return v___f_178_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_4808__overap_209_; lean_object* v___x_210_; 
v___x_190_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_191_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1);
v___f_192_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_192_, 0, v___x_190_);
lean_closure_set(v___f_192_, 1, v___f_191_);
v___x_193_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_194_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_195_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_195_, 0, v___x_193_);
lean_closure_set(v___f_195_, 1, v___f_194_);
v___f_196_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_198_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___f_199_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7));
v___f_200_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8));
v___f_201_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9));
v___f_202_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10));
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___f_196_);
lean_ctor_set(v___x_203_, 1, v___f_197_);
v___x_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___f_198_);
lean_ctor_set(v___x_204_, 2, v___f_199_);
lean_ctor_set(v___x_204_, 3, v___f_200_);
lean_ctor_set(v___x_204_, 4, v___f_201_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___f_202_);
v___x_206_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_192_, v___f_195_, v___x_205_);
v___x_207_ = l_Lean_instInhabitedExpr;
v___x_208_ = l_instInhabitedOfMonad___redArg(v___x_206_, v___x_207_);
v___x_4808__overap_209_ = lean_panic_fn_borrowed(v___x_208_, v_msg_188_);
lean_dec(v___x_208_);
v___x_210_ = lean_apply_1(v___x_4808__overap_209_, v___y_189_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_key_214_; lean_object* v_value_215_; lean_object* v_tail_216_; uint8_t v___y_218_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v_fst_223_; lean_object* v_snd_224_; uint8_t v___x_225_; 
v_key_214_ = lean_ctor_get(v_x_212_, 0);
v_value_215_ = lean_ctor_get(v_x_212_, 1);
v_tail_216_ = lean_ctor_get(v_x_212_, 2);
v_fst_221_ = lean_ctor_get(v_key_214_, 0);
v_snd_222_ = lean_ctor_get(v_key_214_, 1);
v_fst_223_ = lean_ctor_get(v_a_211_, 0);
v_snd_224_ = lean_ctor_get(v_a_211_, 1);
v___x_225_ = l_Lean_ExprStructEq_beq(v_fst_221_, v_fst_223_);
if (v___x_225_ == 0)
{
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_eq(v_snd_222_, v_snd_224_);
v___y_218_ = v___x_226_;
goto v___jp_217_;
}
v___jp_217_:
{
if (v___y_218_ == 0)
{
v_x_212_ = v_tail_216_;
goto _start;
}
else
{
lean_object* v___x_220_; 
lean_inc(v_value_215_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_value_215_);
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_227_, v_x_228_);
lean_dec(v_x_228_);
lean_dec_ref(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object* v_m_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_buckets_232_; lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v_fold_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_buckets_232_ = lean_ctor_get(v_m_230_, 1);
v_fst_233_ = lean_ctor_get(v_a_231_, 0);
v_snd_234_ = lean_ctor_get(v_a_231_, 1);
v___x_235_ = lean_array_get_size(v_buckets_232_);
v___x_236_ = l_Lean_ExprStructEq_hash(v_fst_233_);
v___x_237_ = lean_uint64_of_nat(v_snd_234_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
v___x_239_ = 32ULL;
v___x_240_ = lean_uint64_shift_right(v___x_238_, v___x_239_);
v_fold_241_ = lean_uint64_xor(v___x_238_, v___x_240_);
v___x_242_ = 16ULL;
v___x_243_ = lean_uint64_shift_right(v_fold_241_, v___x_242_);
v___x_244_ = lean_uint64_xor(v_fold_241_, v___x_243_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = lean_usize_of_nat(v___x_235_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_sub(v___x_246_, v___x_247_);
v___x_249_ = lean_usize_land(v___x_245_, v___x_248_);
v___x_250_ = lean_array_uget_borrowed(v_buckets_232_, v___x_249_);
v___x_251_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_231_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object* v_m_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_252_, v_a_253_);
lean_dec_ref(v_a_253_);
lean_dec_ref(v_m_252_);
return v_res_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_259_ = lean_unsigned_to_nat(21u);
v___x_260_ = lean_unsigned_to_nat(96u);
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_263_ = l_mkPanicMessageWithDecl(v___x_262_, v___x_261_, v___x_260_, v___x_259_, v___x_258_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_265_ = lean_unsigned_to_nat(21u);
v___x_266_ = lean_unsigned_to_nat(97u);
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_269_ = l_mkPanicMessageWithDecl(v___x_268_, v___x_267_, v___x_266_, v___x_265_, v___x_264_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_271_ = lean_unsigned_to_nat(21u);
v___x_272_ = lean_unsigned_to_nat(98u);
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_275_ = l_mkPanicMessageWithDecl(v___x_274_, v___x_273_, v___x_272_, v___x_271_, v___x_270_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_277_ = lean_unsigned_to_nat(21u);
v___x_278_ = lean_unsigned_to_nat(95u);
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_281_ = l_mkPanicMessageWithDecl(v___x_280_, v___x_279_, v___x_278_, v___x_277_, v___x_276_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object* v_start_282_, lean_object* v_stop_283_, lean_object* v_args_284_, lean_object* v_e_285_, lean_object* v_offset_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = l_Lean_Expr_looseBVarRange(v_e_285_);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_offset_286_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
if (lean_obj_tag(v_e_285_) == 5)
{
lean_object* v_fn_290_; lean_object* v_arg_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_fn_290_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_fn_290_);
v_arg_291_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_arg_291_);
lean_inc(v_offset_286_);
lean_inc_ref(v_e_285_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_e_285_);
lean_ctor_set(v___x_292_, 1, v_offset_286_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_287_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; lean_object* v_fst_295_; lean_object* v_snd_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v___x_294_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_282_, v_stop_283_, v_args_284_, v_e_285_, v_fn_290_, v_arg_291_, v_offset_286_, v_a_287_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
v_snd_296_ = lean_ctor_get(v___x_294_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snd_296_);
lean_inc(v_fst_295_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_inc(v_fst_295_);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_296_, v___x_292_, v_fst_295_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_fst_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_val_305_; lean_object* v___x_306_; 
lean_dec_ref_known(v___x_292_, 2);
lean_dec_ref(v_arg_291_);
lean_dec_ref_known(v_e_285_, 2);
lean_dec_ref(v_fn_290_);
lean_dec(v_offset_286_);
v_val_305_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_293_, 1);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_val_305_);
lean_ctor_set(v___x_306_, 1, v_a_287_);
return v___x_306_;
}
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_e_285_, v_offset_286_, v_a_287_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec(v_offset_286_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_e_285_);
lean_ctor_set(v___x_308_, 1, v_a_287_);
return v___x_308_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2));
v___x_313_ = lean_unsigned_to_nat(18u);
v___x_314_ = lean_unsigned_to_nat(1847u);
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_317_ = l_mkPanicMessageWithDecl(v___x_316_, v___x_315_, v___x_314_, v___x_313_, v___x_312_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_318_, lean_object* v_stop_319_, lean_object* v_args_320_, lean_object* v_e_321_, lean_object* v_f_322_, lean_object* v_a_323_, lean_object* v_offset_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_329_; 
lean_inc(v_offset_324_);
v___x_326_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_318_, v_stop_319_, v_args_320_, v_f_322_, v_offset_324_, v_a_325_);
v_fst_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v___x_326_);
v___x_329_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_318_, v_stop_319_, v_args_320_, v_a_323_, v_offset_324_, v_snd_328_);
if (lean_obj_tag(v_e_321_) == 5)
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_354_; 
v_fst_330_ = lean_ctor_get(v___x_329_, 0);
v_snd_331_ = lean_ctor_get(v___x_329_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_354_ == 0)
{
v___x_333_ = v___x_329_;
v_isShared_334_ = v_isSharedCheck_354_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_330_);
lean_dec(v___x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_354_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fn_335_; lean_object* v_arg_336_; size_t v___x_337_; size_t v___x_338_; uint8_t v___x_339_; 
v_fn_335_ = lean_ctor_get(v_e_321_, 0);
v_arg_336_ = lean_ctor_get(v_e_321_, 1);
v___x_337_ = lean_ptr_addr(v_fn_335_);
v___x_338_ = lean_ptr_addr(v_fst_327_);
v___x_339_ = lean_usize_dec_eq(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_342_; 
lean_dec_ref_known(v_e_321_, 2);
v___x_340_ = l_Lean_Expr_app___override(v_fst_327_, v_fst_330_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_snd_331_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
else
{
size_t v___x_344_; size_t v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_ptr_addr(v_arg_336_);
v___x_345_ = lean_ptr_addr(v_fst_330_);
v___x_346_ = lean_usize_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec_ref_known(v_e_321_, 2);
v___x_347_ = l_Lean_Expr_app___override(v_fst_327_, v_fst_330_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_347_);
v___x_349_ = v___x_333_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_snd_331_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
else
{
lean_object* v___x_352_; 
lean_dec(v_fst_330_);
lean_dec(v_fst_327_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_e_321_);
v___x_352_ = v___x_333_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_e_321_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_snd_331_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v_snd_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_fst_327_);
lean_dec_ref(v_e_321_);
v_snd_355_ = lean_ctor_get(v___x_329_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_365_);
v___x_357_ = v___x_329_;
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snd_355_);
lean_dec(v___x_329_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_360_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_359_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_snd_355_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_367_ = lean_unsigned_to_nat(21u);
v___x_368_ = lean_unsigned_to_nat(99u);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_371_ = l_mkPanicMessageWithDecl(v___x_370_, v___x_369_, v___x_368_, v___x_367_, v___x_366_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_372_, lean_object* v_stop_373_, lean_object* v_args_374_, lean_object* v_e_375_, lean_object* v_offset_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = l_Lean_Expr_looseBVarRange(v_e_375_);
v___x_379_ = lean_nat_dec_le(v___x_378_, v_offset_376_);
lean_dec(v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v___y_387_; lean_object* v___x_390_; 
lean_inc(v_offset_376_);
lean_inc_ref(v_e_375_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_e_375_);
lean_ctor_set(v___x_380_, 1, v_offset_376_);
v___x_390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_377_, v___x_380_);
if (lean_obj_tag(v___x_390_) == 0)
{
switch(lean_obj_tag(v_e_375_))
{
case 0:
{
lean_object* v_deBruijnIndex_391_; lean_object* v___x_392_; 
v_deBruijnIndex_391_ = lean_ctor_get(v_e_375_, 0);
lean_inc(v_deBruijnIndex_391_);
lean_dec_ref_known(v_e_375_, 1);
v___x_392_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_372_, v_stop_373_, v_args_374_, v_deBruijnIndex_391_, v_offset_376_);
lean_dec(v_offset_376_);
lean_dec(v_deBruijnIndex_391_);
v_fst_382_ = v___x_392_;
v_snd_383_ = v_a_377_;
goto v___jp_381_;
}
case 1:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref_known(v_e_375_, 1);
lean_dec(v_offset_376_);
v___x_393_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_394_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_393_, v_a_377_);
v___y_387_ = v___x_394_;
goto v___jp_386_;
}
case 2:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref_known(v_e_375_, 1);
lean_dec(v_offset_376_);
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_396_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_395_, v_a_377_);
v___y_387_ = v___x_396_;
goto v___jp_386_;
}
case 3:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref_known(v_e_375_, 1);
lean_dec(v_offset_376_);
v___x_397_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_398_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_397_, v_a_377_);
v___y_387_ = v___x_398_;
goto v___jp_386_;
}
case 4:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref_known(v_e_375_, 2);
lean_dec(v_offset_376_);
v___x_399_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_400_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_399_, v_a_377_);
v___y_387_ = v___x_400_;
goto v___jp_386_;
}
case 5:
{
lean_object* v_fn_401_; lean_object* v_arg_402_; lean_object* v_head_403_; uint8_t v___x_404_; 
v_fn_401_ = lean_ctor_get(v_e_375_, 0);
v_arg_402_ = lean_ctor_get(v_e_375_, 1);
v_head_403_ = l_Lean_Expr_getAppFn(v_e_375_);
v___x_404_ = l_Lean_Expr_isBVar(v_head_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_inc_ref(v_arg_402_);
lean_inc_ref(v_fn_401_);
lean_dec_ref(v_head_403_);
v___x_405_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_372_, v_stop_373_, v_args_374_, v_e_375_, v_fn_401_, v_arg_402_, v_offset_376_, v_a_377_);
v___y_387_ = v___x_405_;
goto v___jp_386_;
}
else
{
lean_object* v___x_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; size_t v_sz_412_; size_t v___x_413_; lean_object* v___x_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_417_; 
lean_inc(v_offset_376_);
v___x_406_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_head_403_, v_offset_376_, v_a_377_);
v_fst_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_snd_408_);
lean_dec_ref(v___x_406_);
v___x_409_ = l_Lean_Expr_getAppNumArgs(v_e_375_);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
lean_dec(v___x_409_);
v___x_411_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_375_, v___x_410_);
v_sz_412_ = lean_array_size(v___x_411_);
v___x_413_ = ((size_t)0ULL);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_372_, v_stop_373_, v_args_374_, v_offset_376_, v_sz_412_, v___x_413_, v___x_411_, v_snd_408_);
v_fst_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_snd_416_);
lean_dec_ref(v___x_414_);
v___x_417_ = l_Lean_Expr_betaRev(v_fst_407_, v_fst_415_, v___x_379_, v___x_379_);
lean_dec(v_fst_415_);
v_fst_382_ = v___x_417_;
v_snd_383_ = v_snd_416_;
goto v___jp_381_;
}
}
case 6:
{
lean_object* v_binderName_418_; lean_object* v_binderType_419_; lean_object* v_body_420_; uint8_t v_binderInfo_421_; lean_object* v___x_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; size_t v___x_430_; size_t v___x_431_; uint8_t v___x_432_; 
v_binderName_418_ = lean_ctor_get(v_e_375_, 0);
v_binderType_419_ = lean_ctor_get(v_e_375_, 1);
v_body_420_ = lean_ctor_get(v_e_375_, 2);
v_binderInfo_421_ = lean_ctor_get_uint8(v_e_375_, sizeof(void*)*3 + 8);
lean_inc(v_offset_376_);
lean_inc_ref(v_binderType_419_);
v___x_422_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_binderType_419_, v_offset_376_, v_a_377_);
v_fst_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___x_422_);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_add(v_offset_376_, v___x_425_);
lean_dec(v_offset_376_);
lean_inc_ref(v_body_420_);
v___x_427_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_body_420_, v___x_426_, v_snd_424_);
v_fst_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_snd_429_);
lean_dec_ref(v___x_427_);
v___x_430_ = lean_ptr_addr(v_binderType_419_);
v___x_431_ = lean_ptr_addr(v_fst_423_);
v___x_432_ = lean_usize_dec_eq(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_inc(v_binderName_418_);
lean_dec_ref_known(v_e_375_, 3);
v___x_433_ = l_Lean_Expr_lam___override(v_binderName_418_, v_fst_423_, v_fst_428_, v_binderInfo_421_);
v_fst_382_ = v___x_433_;
v_snd_383_ = v_snd_429_;
goto v___jp_381_;
}
else
{
size_t v___x_434_; size_t v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_ptr_addr(v_body_420_);
v___x_435_ = lean_ptr_addr(v_fst_428_);
v___x_436_ = lean_usize_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
lean_inc(v_binderName_418_);
lean_dec_ref_known(v_e_375_, 3);
v___x_437_ = l_Lean_Expr_lam___override(v_binderName_418_, v_fst_423_, v_fst_428_, v_binderInfo_421_);
v_fst_382_ = v___x_437_;
v_snd_383_ = v_snd_429_;
goto v___jp_381_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_421_, v_binderInfo_421_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_inc(v_binderName_418_);
lean_dec_ref_known(v_e_375_, 3);
v___x_439_ = l_Lean_Expr_lam___override(v_binderName_418_, v_fst_423_, v_fst_428_, v_binderInfo_421_);
v_fst_382_ = v___x_439_;
v_snd_383_ = v_snd_429_;
goto v___jp_381_;
}
else
{
lean_dec(v_fst_428_);
lean_dec(v_fst_423_);
v_fst_382_ = v_e_375_;
v_snd_383_ = v_snd_429_;
goto v___jp_381_;
}
}
}
}
case 7:
{
lean_object* v_binderName_440_; lean_object* v_binderType_441_; lean_object* v_body_442_; uint8_t v_binderInfo_443_; lean_object* v___x_444_; lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v_binderName_440_ = lean_ctor_get(v_e_375_, 0);
v_binderType_441_ = lean_ctor_get(v_e_375_, 1);
v_body_442_ = lean_ctor_get(v_e_375_, 2);
v_binderInfo_443_ = lean_ctor_get_uint8(v_e_375_, sizeof(void*)*3 + 8);
lean_inc(v_offset_376_);
lean_inc_ref(v_binderType_441_);
v___x_444_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_binderType_441_, v_offset_376_, v_a_377_);
v_fst_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_snd_446_);
lean_dec_ref(v___x_444_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_offset_376_, v___x_447_);
lean_dec(v_offset_376_);
lean_inc_ref(v_body_442_);
v___x_449_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_body_442_, v___x_448_, v_snd_446_);
v_fst_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_snd_451_);
lean_dec_ref(v___x_449_);
v___x_452_ = lean_ptr_addr(v_binderType_441_);
v___x_453_ = lean_ptr_addr(v_fst_445_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_inc(v_binderName_440_);
lean_dec_ref_known(v_e_375_, 3);
v___x_455_ = l_Lean_Expr_forallE___override(v_binderName_440_, v_fst_445_, v_fst_450_, v_binderInfo_443_);
v_fst_382_ = v___x_455_;
v_snd_383_ = v_snd_451_;
goto v___jp_381_;
}
else
{
size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_ptr_addr(v_body_442_);
v___x_457_ = lean_ptr_addr(v_fst_450_);
v___x_458_ = lean_usize_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_inc(v_binderName_440_);
lean_dec_ref_known(v_e_375_, 3);
v___x_459_ = l_Lean_Expr_forallE___override(v_binderName_440_, v_fst_445_, v_fst_450_, v_binderInfo_443_);
v_fst_382_ = v___x_459_;
v_snd_383_ = v_snd_451_;
goto v___jp_381_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_443_, v_binderInfo_443_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_inc(v_binderName_440_);
lean_dec_ref_known(v_e_375_, 3);
v___x_461_ = l_Lean_Expr_forallE___override(v_binderName_440_, v_fst_445_, v_fst_450_, v_binderInfo_443_);
v_fst_382_ = v___x_461_;
v_snd_383_ = v_snd_451_;
goto v___jp_381_;
}
else
{
lean_dec(v_fst_450_);
lean_dec(v_fst_445_);
v_fst_382_ = v_e_375_;
v_snd_383_ = v_snd_451_;
goto v___jp_381_;
}
}
}
}
case 8:
{
lean_object* v_declName_462_; lean_object* v_type_463_; lean_object* v_value_464_; lean_object* v_body_465_; uint8_t v_nondep_466_; lean_object* v___x_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v_declName_462_ = lean_ctor_get(v_e_375_, 0);
v_type_463_ = lean_ctor_get(v_e_375_, 1);
v_value_464_ = lean_ctor_get(v_e_375_, 2);
v_body_465_ = lean_ctor_get(v_e_375_, 3);
v_nondep_466_ = lean_ctor_get_uint8(v_e_375_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_376_, 2);
lean_inc_ref(v_type_463_);
v___x_467_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_type_463_, v_offset_376_, v_a_377_);
v_fst_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_fst_468_);
v_snd_469_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_469_);
lean_dec_ref(v___x_467_);
lean_inc_ref(v_value_464_);
v___x_470_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_value_464_, v_offset_376_, v_snd_469_);
v_fst_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v___x_470_, 1);
lean_inc(v_snd_472_);
lean_dec_ref(v___x_470_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_offset_376_, v___x_473_);
lean_dec(v_offset_376_);
lean_inc_ref(v_body_465_);
v___x_475_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_body_465_, v___x_474_, v_snd_472_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_snd_477_);
lean_dec_ref(v___x_475_);
v___x_478_ = lean_ptr_addr(v_type_463_);
v___x_479_ = lean_ptr_addr(v_fst_468_);
v___x_480_ = lean_usize_dec_eq(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_inc(v_declName_462_);
lean_dec_ref_known(v_e_375_, 4);
v___x_481_ = l_Lean_Expr_letE___override(v_declName_462_, v_fst_468_, v_fst_471_, v_fst_476_, v_nondep_466_);
v_fst_382_ = v___x_481_;
v_snd_383_ = v_snd_477_;
goto v___jp_381_;
}
else
{
size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_ptr_addr(v_value_464_);
v___x_483_ = lean_ptr_addr(v_fst_471_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_inc(v_declName_462_);
lean_dec_ref_known(v_e_375_, 4);
v___x_485_ = l_Lean_Expr_letE___override(v_declName_462_, v_fst_468_, v_fst_471_, v_fst_476_, v_nondep_466_);
v_fst_382_ = v___x_485_;
v_snd_383_ = v_snd_477_;
goto v___jp_381_;
}
else
{
size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_ptr_addr(v_body_465_);
v___x_487_ = lean_ptr_addr(v_fst_476_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_inc(v_declName_462_);
lean_dec_ref_known(v_e_375_, 4);
v___x_489_ = l_Lean_Expr_letE___override(v_declName_462_, v_fst_468_, v_fst_471_, v_fst_476_, v_nondep_466_);
v_fst_382_ = v___x_489_;
v_snd_383_ = v_snd_477_;
goto v___jp_381_;
}
else
{
lean_dec(v_fst_476_);
lean_dec(v_fst_471_);
lean_dec(v_fst_468_);
v_fst_382_ = v_e_375_;
v_snd_383_ = v_snd_477_;
goto v___jp_381_;
}
}
}
}
case 9:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref_known(v_e_375_, 1);
lean_dec(v_offset_376_);
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_491_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_490_, v_a_377_);
v___y_387_ = v___x_491_;
goto v___jp_386_;
}
case 10:
{
lean_object* v_data_492_; lean_object* v_expr_493_; lean_object* v___x_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v_data_492_ = lean_ctor_get(v_e_375_, 0);
v_expr_493_ = lean_ctor_get(v_e_375_, 1);
lean_inc_ref(v_expr_493_);
v___x_494_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_expr_493_, v_offset_376_, v_a_377_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_496_);
lean_dec_ref(v___x_494_);
v___x_497_ = lean_ptr_addr(v_expr_493_);
v___x_498_ = lean_ptr_addr(v_fst_495_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_inc(v_data_492_);
lean_dec_ref_known(v_e_375_, 2);
v___x_500_ = l_Lean_Expr_mdata___override(v_data_492_, v_fst_495_);
v_fst_382_ = v___x_500_;
v_snd_383_ = v_snd_496_;
goto v___jp_381_;
}
else
{
lean_dec(v_fst_495_);
v_fst_382_ = v_e_375_;
v_snd_383_ = v_snd_496_;
goto v___jp_381_;
}
}
default: 
{
lean_object* v_typeName_501_; lean_object* v_idx_502_; lean_object* v_struct_503_; lean_object* v___x_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v_typeName_501_ = lean_ctor_get(v_e_375_, 0);
v_idx_502_ = lean_ctor_get(v_e_375_, 1);
v_struct_503_ = lean_ctor_get(v_e_375_, 2);
lean_inc_ref(v_struct_503_);
v___x_504_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_372_, v_stop_373_, v_args_374_, v_struct_503_, v_offset_376_, v_a_377_);
v_fst_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_fst_505_);
v_snd_506_ = lean_ctor_get(v___x_504_, 1);
lean_inc(v_snd_506_);
lean_dec_ref(v___x_504_);
v___x_507_ = lean_ptr_addr(v_struct_503_);
v___x_508_ = lean_ptr_addr(v_fst_505_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_inc(v_idx_502_);
lean_inc(v_typeName_501_);
lean_dec_ref_known(v_e_375_, 3);
v___x_510_ = l_Lean_Expr_proj___override(v_typeName_501_, v_idx_502_, v_fst_505_);
v_fst_382_ = v___x_510_;
v_snd_383_ = v_snd_506_;
goto v___jp_381_;
}
else
{
lean_dec(v_fst_505_);
v_fst_382_ = v_e_375_;
v_snd_383_ = v_snd_506_;
goto v___jp_381_;
}
}
}
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; 
lean_dec_ref_known(v___x_380_, 2);
lean_dec(v_offset_376_);
lean_dec_ref(v_e_375_);
v_val_511_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v___x_390_, 1);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_val_511_);
lean_ctor_set(v___x_512_, 1, v_a_377_);
return v___x_512_;
}
v___jp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc_ref(v_fst_382_);
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_383_, v___x_380_, v_fst_382_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_fst_382_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
return v___x_385_;
}
v___jp_386_:
{
lean_object* v_fst_388_; lean_object* v_snd_389_; 
v_fst_388_ = lean_ctor_get(v___y_387_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v___y_387_, 1);
lean_inc(v_snd_389_);
lean_dec_ref(v___y_387_);
v_fst_382_ = v_fst_388_;
v_snd_383_ = v_snd_389_;
goto v___jp_381_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec(v_offset_376_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_e_375_);
lean_ctor_set(v___x_513_, 1, v_a_377_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_514_, lean_object* v_stop_515_, lean_object* v_args_516_, lean_object* v_offset_517_, size_t v_sz_518_, size_t v_i_519_, lean_object* v_bs_520_, lean_object* v___y_521_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_offset_517_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_bs_520_);
lean_ctor_set(v___x_523_, 1, v___y_521_);
return v___x_523_;
}
else
{
lean_object* v_v_524_; lean_object* v___x_525_; lean_object* v_fst_526_; lean_object* v_snd_527_; lean_object* v___x_528_; lean_object* v_bs_x27_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v_v_524_ = lean_array_uget_borrowed(v_bs_520_, v_i_519_);
lean_inc(v_offset_517_);
lean_inc(v_v_524_);
v___x_525_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_514_, v_stop_515_, v_args_516_, v_v_524_, v_offset_517_, v___y_521_);
v_fst_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_fst_526_);
v_snd_527_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_snd_527_);
lean_dec_ref(v___x_525_);
v___x_528_ = lean_unsigned_to_nat(0u);
v_bs_x27_529_ = lean_array_uset(v_bs_520_, v_i_519_, v___x_528_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_519_, v___x_530_);
v___x_532_ = lean_array_uset(v_bs_x27_529_, v_i_519_, v_fst_526_);
v_i_519_ = v___x_531_;
v_bs_520_ = v___x_532_;
v___y_521_ = v_snd_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_534_, lean_object* v_stop_535_, lean_object* v_args_536_, lean_object* v_offset_537_, lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_bs_540_, lean_object* v___y_541_){
_start:
{
size_t v_sz_boxed_542_; size_t v_i_boxed_543_; lean_object* v_res_544_; 
v_sz_boxed_542_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_543_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_534_, v_stop_535_, v_args_536_, v_offset_537_, v_sz_boxed_542_, v_i_boxed_543_, v_bs_540_, v___y_541_);
lean_dec_ref(v_args_536_);
lean_dec(v_stop_535_);
lean_dec(v_start_534_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_545_, lean_object* v_stop_546_, lean_object* v_args_547_, lean_object* v_e_548_, lean_object* v_offset_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_545_, v_stop_546_, v_args_547_, v_e_548_, v_offset_549_, v_a_550_);
lean_dec_ref(v_args_547_);
lean_dec(v_stop_546_);
lean_dec(v_start_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_552_, lean_object* v_stop_553_, lean_object* v_args_554_, lean_object* v_e_555_, lean_object* v_f_556_, lean_object* v_a_557_, lean_object* v_offset_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_552_, v_stop_553_, v_args_554_, v_e_555_, v_f_556_, v_a_557_, v_offset_558_, v_a_559_);
lean_dec_ref(v_args_554_);
lean_dec(v_stop_553_);
lean_dec(v_start_552_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_561_, lean_object* v_stop_562_, lean_object* v_args_563_, lean_object* v_e_564_, lean_object* v_offset_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_561_, v_stop_562_, v_args_563_, v_e_564_, v_offset_565_, v_a_566_);
lean_dec_ref(v_args_563_);
lean_dec(v_stop_562_);
lean_dec(v_start_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_568_, lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_569_, v_a_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_572_, v_m_573_, v_a_574_);
lean_dec_ref(v_a_574_);
lean_dec_ref(v_m_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_576_, lean_object* v_m_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_577_, v_a_578_, v_b_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_581_, lean_object* v_a_582_, lean_object* v_x_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_582_, v_x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_585_, lean_object* v_a_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_585_, v_a_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec_ref(v_a_586_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_589_, lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_593_, lean_object* v_a_594_, lean_object* v_x_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_593_, v_a_594_, v_x_595_);
lean_dec(v_x_595_);
lean_dec_ref(v_a_594_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object* v_00_u03b2_598_, lean_object* v_data_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_data_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object* v_00_u03b2_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_602_, v_b_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_606_, lean_object* v_i_607_, lean_object* v_source_608_, lean_object* v_target_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v_i_607_, v_source_608_, v_target_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_615_, size_t v_i_616_, size_t v_stop_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_eq(v_i_616_, v_stop_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_array_uget_borrowed(v_as_615_, v_i_616_);
v___x_620_ = l_Lean_Expr_consumeMData(v___x_619_);
v___x_621_ = l_Lean_Expr_isLambda(v___x_620_);
lean_dec_ref(v___x_620_);
if (v___x_621_ == 0)
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_616_, v___x_622_);
v_i_616_ = v___x_623_;
goto _start;
}
else
{
return v___x_621_;
}
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_){
_start:
{
size_t v_i_boxed_629_; size_t v_stop_boxed_630_; uint8_t v_res_631_; lean_object* v_r_632_; 
v_i_boxed_629_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_630_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_626_, v_i_boxed_629_, v_stop_boxed_630_);
lean_dec_ref(v_as_626_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = lean_unsigned_to_nat(16u);
v___x_635_ = lean_mk_array(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__0, &l_Lean_Expr_instantiateBetaRevRange___closed__0_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__0);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__3));
v___x_642_ = lean_unsigned_to_nat(4u);
v___x_643_ = lean_unsigned_to_nat(39u);
v___x_644_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__2));
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_646_ = l_mkPanicMessageWithDecl(v___x_645_, v___x_644_, v___x_643_, v___x_642_, v___x_641_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_647_, lean_object* v_start_648_, lean_object* v_stop_649_, lean_object* v_args_650_){
_start:
{
lean_object* v___y_652_; uint8_t v___y_664_; uint8_t v___x_671_; 
v___x_671_ = l_Lean_Expr_hasLooseBVars(v_e_647_);
if (v___x_671_ == 0)
{
v___y_664_ = v___x_671_;
goto v___jp_663_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_nat_dec_lt(v_start_648_, v_stop_649_);
v___y_664_ = v___x_672_;
goto v___jp_663_;
}
v___jp_651_:
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_lt(v_start_648_, v___y_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v___y_652_);
v___x_654_ = lean_expr_instantiate_rev_range(v_e_647_, v_start_648_, v_stop_649_, v_args_650_);
lean_dec(v_stop_649_);
lean_dec_ref(v_e_647_);
return v___x_654_;
}
else
{
size_t v___x_655_; size_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_usize_of_nat(v_start_648_);
v___x_656_ = lean_usize_of_nat(v___y_652_);
lean_dec(v___y_652_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_650_, v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_expr_instantiate_rev_range(v_e_647_, v_start_648_, v_stop_649_, v_args_650_);
lean_dec(v_stop_649_);
lean_dec_ref(v_e_647_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_fst_662_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__1, &l_Lean_Expr_instantiateBetaRevRange___closed__1_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__1);
v___x_661_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_648_, v_stop_649_, v_args_650_, v_e_647_, v___x_659_, v___x_660_);
lean_dec(v_stop_649_);
v_fst_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_fst_662_);
lean_dec_ref(v___x_661_);
return v_fst_662_;
}
}
}
v___jp_663_:
{
if (v___y_664_ == 0)
{
lean_dec(v_stop_649_);
return v_e_647_;
}
else
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_array_get_size(v_args_650_);
v___x_666_ = lean_nat_dec_le(v_stop_649_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_stop_649_);
lean_dec_ref(v_e_647_);
v___x_667_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_668_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_667_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v_start_648_, v_stop_649_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_expr_instantiate_rev_range(v_e_647_, v_start_648_, v_stop_649_, v_args_650_);
lean_dec(v_stop_649_);
lean_dec_ref(v_e_647_);
return v___x_670_;
}
else
{
if (v___x_666_ == 0)
{
v___y_652_ = v___x_665_;
goto v___jp_651_;
}
else
{
lean_inc(v_stop_649_);
v___y_652_ = v_stop_649_;
goto v___jp_651_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_673_, lean_object* v_start_674_, lean_object* v_stop_675_, lean_object* v_args_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Expr_instantiateBetaRevRange(v_e_673_, v_start_674_, v_stop_675_, v_args_676_);
lean_dec_ref(v_args_676_);
lean_dec(v_start_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v_env_685_; lean_object* v___x_686_; lean_object* v_toCold_687_; lean_object* v_mctx_688_; lean_object* v_lctx_689_; lean_object* v_options_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_684_ = lean_st_ref_get(v___y_682_);
v_env_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_env_685_);
lean_dec(v___x_684_);
v___x_686_ = lean_st_ref_get(v___y_680_);
v_toCold_687_ = lean_ctor_get(v___y_681_, 0);
v_mctx_688_ = lean_ctor_get(v___x_686_, 0);
lean_inc_ref(v_mctx_688_);
lean_dec(v___x_686_);
v_lctx_689_ = lean_ctor_get(v___y_679_, 2);
v_options_690_ = lean_ctor_get(v_toCold_687_, 2);
lean_inc_ref(v_options_690_);
lean_inc_ref(v_lctx_689_);
v___x_691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_691_, 0, v_env_685_);
lean_ctor_set(v___x_691_, 1, v_mctx_688_);
lean_ctor_set(v___x_691_, 2, v_lctx_689_);
lean_ctor_set(v___x_691_, 3, v_options_690_);
v___x_692_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_msgData_678_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_ref_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_ref_707_ = lean_ctor_get(v___y_704_, 2);
v___x_708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_inc(v_ref_707_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_707_);
lean_ctor_set(v___x_713_, 1, v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_735_ = l_Lean_indentExpr(v_f_728_);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_736_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_745_, lean_object* v_f_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_753_, lean_object* v_f_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_753_, v_f_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_761_, lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_769_, v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_777_, lean_object* v_args_778_, lean_object* v_f_779_, lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_a_788_; uint8_t v___x_792_; 
v___x_792_ = lean_nat_dec_lt(v_a_780_, v_upperBound_777_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_a_780_);
lean_dec_ref(v_f_779_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_b_781_);
return v___x_793_;
}
else
{
lean_object* v_fst_794_; 
v_fst_794_ = lean_ctor_get(v_b_781_, 0);
lean_inc(v_fst_794_);
if (lean_obj_tag(v_fst_794_) == 7)
{
lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_snd_795_ = lean_ctor_get(v_b_781_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_b_781_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_b_781_, 0);
lean_dec(v_unused_804_);
v___x_797_ = v_b_781_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_dec(v_b_781_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_body_799_; lean_object* v___x_801_; 
v_body_799_ = lean_ctor_get(v_fst_794_, 2);
lean_inc_ref(v_body_799_);
lean_dec_ref_known(v_fst_794_, 3);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_body_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_body_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_795_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v_a_788_ = v___x_801_;
goto v___jp_787_;
}
}
}
else
{
lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_840_; 
v_snd_805_ = lean_ctor_get(v_b_781_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_b_781_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_b_781_, 0);
lean_dec(v_unused_841_);
v___x_807_ = v_b_781_;
v_isShared_808_ = v_isSharedCheck_840_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_dec(v_b_781_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_840_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc(v_a_780_);
lean_inc(v_fst_794_);
v___x_809_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_794_, v_snd_805_, v_a_780_, v_args_778_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
v___x_810_ = lean_whnf(v___x_809_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
if (lean_obj_tag(v_a_811_) == 7)
{
lean_object* v_body_812_; lean_object* v___x_814_; 
lean_dec(v_snd_805_);
lean_dec(v_fst_794_);
v_body_812_ = lean_ctor_get(v_a_811_, 2);
lean_inc_ref(v_body_812_);
lean_dec_ref_known(v_a_811_, 3);
lean_inc(v_a_780_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_a_780_);
lean_ctor_set(v___x_807_, 0, v_body_812_);
v___x_814_ = v___x_807_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_body_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_a_780_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
v_a_788_ = v___x_814_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v_a_811_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_a_780_, v___x_817_);
lean_inc_ref(v_f_779_);
v___x_819_ = l_Lean_mkAppRange(v_f_779_, v___x_816_, v___x_818_, v_args_778_);
lean_dec(v___x_818_);
v___x_820_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_819_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_822_; 
lean_dec_ref_known(v___x_820_, 1);
if (v_isShared_808_ == 0)
{
v___x_822_ = v___x_807_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_794_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_805_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v_a_788_ = v___x_822_;
goto v___jp_787_;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
lean_dec(v_fst_794_);
lean_dec(v_a_780_);
lean_dec_ref(v_f_779_);
v_a_824_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_820_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_820_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
lean_dec(v_fst_794_);
lean_dec(v_a_780_);
lean_dec_ref(v_f_779_);
v_a_832_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_810_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_810_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
v___jp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_a_780_, v___x_789_);
lean_dec(v_a_780_);
v_a_780_ = v___x_790_;
v_b_781_ = v_a_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_842_, lean_object* v_args_843_, lean_object* v_f_844_, lean_object* v_a_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_842_, v_args_843_, v_f_844_, v_a_845_, v_b_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v_args_843_);
lean_dec(v_upperBound_842_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_853_, lean_object* v_args_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; 
lean_inc(v_a_858_);
lean_inc_ref(v_a_857_);
lean_inc(v_a_856_);
lean_inc_ref(v_a_855_);
lean_inc_ref(v_f_853_);
v___x_860_ = lean_infer_type(v_f_853_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_array_get_size(v_args_854_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_a_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_862_, v_args_854_, v_f_853_, v___x_863_, v___x_864_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_fst_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_fst_870_);
v_snd_871_ = lean_ctor_get(v_a_866_, 1);
lean_inc(v_snd_871_);
lean_dec(v_a_866_);
v___x_872_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_870_, v_snd_871_, v___x_862_, v_args_854_);
lean_dec(v_snd_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_865_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_865_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_dec_ref(v_f_853_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_885_, lean_object* v_args_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_885_, v_args_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec_ref(v_args_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_893_, lean_object* v_args_894_, lean_object* v_f_895_, lean_object* v_inst_896_, lean_object* v_R_897_, lean_object* v_a_898_, lean_object* v_b_899_, lean_object* v_c_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_893_, v_args_894_, v_f_895_, v_a_898_, v_b_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_907_, lean_object* v_args_908_, lean_object* v_f_909_, lean_object* v_inst_910_, lean_object* v_R_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v_c_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_907_, v_args_908_, v_f_909_, v_inst_910_, v_R_911_, v_a_912_, v_b_913_, v_c_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v_args_908_);
lean_dec(v_upperBound_907_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_924_, lean_object* v_us_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_931_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_932_ = l_Lean_mkConst(v_constName_924_, v_us_925_);
v___x_933_ = l_Lean_MessageData_ofExpr(v___x_932_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_934_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_936_, lean_object* v_us_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_936_, v_us_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_944_, lean_object* v_constName_945_, lean_object* v_us_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_945_, v_us_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_953_, lean_object* v_constName_954_, lean_object* v_us_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_953_, v_constName_954_, v_us_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_toCold_969_; lean_object* v_currRecDepth_970_; lean_object* v_ref_971_; uint8_t v_diag_972_; uint8_t v_suppressElabErrors_973_; lean_object* v_ref_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_toCold_969_ = lean_ctor_get(v___y_966_, 0);
v_currRecDepth_970_ = lean_ctor_get(v___y_966_, 1);
v_ref_971_ = lean_ctor_get(v___y_966_, 2);
v_diag_972_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*3);
v_suppressElabErrors_973_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*3 + 1);
v_ref_974_ = l_Lean_replaceRef(v_ref_962_, v_ref_971_);
lean_inc(v_currRecDepth_970_);
lean_inc_ref(v_toCold_969_);
v___x_975_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_975_, 0, v_toCold_969_);
lean_ctor_set(v___x_975_, 1, v_currRecDepth_970_);
lean_ctor_set(v___x_975_, 2, v_ref_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*3, v_diag_972_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*3 + 1, v_suppressElabErrors_973_);
v___x_976_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_963_, v___y_964_, v___y_965_, v___x_975_, v___y_967_);
lean_dec_ref_known(v___x_975_, 3);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_977_, lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_977_, v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v_ref_977_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
lean_ctor_set(v___x_990_, 3, v___x_989_);
lean_ctor_set(v___x_990_, 4, v___x_988_);
lean_ctor_set(v___x_990_, 5, v___x_988_);
lean_ctor_set(v___x_990_, 6, v___x_988_);
lean_ctor_set(v___x_990_, 7, v___x_988_);
lean_ctor_set(v___x_990_, 8, v___x_988_);
lean_ctor_set(v___x_990_, 9, v___x_988_);
lean_ctor_set(v___x_990_, 10, v___x_988_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_unsigned_to_nat(32u);
v___x_992_ = lean_mk_empty_array_with_capacity(v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_994_ = ((size_t)5ULL);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_unsigned_to_nat(32u);
v___x_997_ = lean_mk_empty_array_with_capacity(v___x_996_);
v___x_998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_999_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v___x_995_);
lean_ctor_set(v___x_999_, 3, v___x_995_);
lean_ctor_set_usize(v___x_999_, 4, v___x_994_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = lean_box(1);
v___x_1001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v___x_1000_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1025_, lean_object* v_declHint_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v_env_1030_; uint8_t v___x_1031_; 
v___x_1029_ = lean_st_ref_get(v___y_1027_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = l_Lean_Name_isAnonymous(v_declHint_1026_);
if (v___x_1031_ == 0)
{
uint8_t v_isExporting_1032_; 
v_isExporting_1032_ = lean_ctor_get_uint8(v_env_1030_, sizeof(void*)*8);
if (v_isExporting_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_env_1030_);
lean_dec(v_declHint_1026_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_msg_1025_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_inc_ref(v_env_1030_);
v___x_1034_ = l_Lean_Environment_setExporting(v_env_1030_, v___x_1031_);
lean_inc(v_declHint_1026_);
lean_inc_ref(v___x_1034_);
v___x_1035_ = l_Lean_Environment_contains(v___x_1034_, v_declHint_1026_, v_isExporting_1032_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_env_1030_);
lean_dec(v_declHint_1026_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_msg_1025_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_c_1042_; lean_object* v___x_1043_; 
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1039_ = l_Lean_Options_empty;
v___x_1040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1034_);
lean_ctor_set(v___x_1040_, 1, v___x_1037_);
lean_ctor_set(v___x_1040_, 2, v___x_1038_);
lean_ctor_set(v___x_1040_, 3, v___x_1039_);
lean_inc(v_declHint_1026_);
v___x_1041_ = l_Lean_MessageData_ofConstName(v_declHint_1026_, v___x_1031_);
v_c_1042_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1042_, 0, v___x_1040_);
lean_ctor_set(v_c_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1030_, v_declHint_1026_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v_env_1030_);
lean_dec(v_declHint_1026_);
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1042_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_note(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_msg_1025_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1086_; 
v_val_1051_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1053_ = v___x_1043_;
v_isShared_1054_ = v_isSharedCheck_1086_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_val_1051_);
lean_dec(v___x_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1086_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mod_1058_; uint8_t v___x_1059_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Lean_Environment_header(v_env_1030_);
lean_dec_ref(v_env_1030_);
v___x_1057_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1056_);
v_mod_1058_ = lean_array_get(v___x_1055_, v___x_1057_, v_val_1051_);
lean_dec(v_val_1051_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_isPrivateName(v_declHint_1026_);
lean_dec(v_declHint_1026_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_c_1042_);
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_MessageData_ofName(v_mod_1058_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_MessageData_note(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_msg_1025_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1069_);
v___x_1071_ = v___x_1053_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_c_1042_);
v___x_1075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_MessageData_ofName(v_mod_1058_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_note(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_msg_1025_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1082_);
v___x_1084_ = v___x_1053_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1087_; 
lean_dec_ref(v_env_1030_);
lean_dec(v_declHint_1026_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_msg_1025_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1088_, lean_object* v_declHint_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1088_, v_declHint_1089_, v___y_1090_);
lean_dec(v___y_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1093_, lean_object* v_declHint_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v___x_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1093_, v_declHint_1094_, v___y_1098_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = l_Lean_unknownIdentifierMessageTag;
v___x_1106_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_a_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1111_, lean_object* v_declHint_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1111_, v_declHint_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1119_, lean_object* v_msg_1120_, lean_object* v_declHint_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_a_1128_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1120_, v_declHint_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1119_, v_a_1128_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1130_, lean_object* v_msg_1131_, lean_object* v_declHint_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1130_, v_msg_1131_, v_declHint_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v_ref_1130_);
return v_res_1138_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1145_, lean_object* v_constName_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1152_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1153_ = 0;
lean_inc(v_constName_1146_);
v___x_1154_ = l_Lean_MessageData_ofConstName(v_constName_1146_, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1145_, v___x_1157_, v_constName_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1159_, lean_object* v_constName_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1159_, v_constName_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_ref_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_ref_1173_; lean_object* v___x_1174_; 
v_ref_1173_ = lean_ctor_get(v___y_1170_, 2);
v___x_1174_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1173_, v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_env_1189_);
lean_dec(v___x_1188_);
v___x_1190_ = 0;
lean_inc(v_constName_1182_);
v___x_1191_ = l_Lean_Environment_findConstVal_x3f(v_env_1189_, v_constName_1182_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_constName_1182_);
v_val_1193_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 0);
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_val_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1208_, lean_object* v_us_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
lean_inc(v_c_1208_);
v___x_1215_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1208_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_levelParams_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_levelParams_1217_ = lean_ctor_get(v_a_1216_, 1);
v___x_1218_ = l_List_lengthTR___redArg(v_levelParams_1217_);
v___x_1219_ = l_List_lengthTR___redArg(v_us_1209_);
v___x_1220_ = lean_nat_dec_eq(v___x_1218_, v___x_1219_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec(v_a_1216_);
v___x_1221_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1208_, v_us_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; 
lean_dec(v_c_1208_);
v___x_1222_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1216_, v_us_1209_, v_a_1213_);
return v___x_1222_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_us_1209_);
lean_dec(v_c_1208_);
v_a_1223_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1215_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1215_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1231_, lean_object* v_us_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1231_, v_us_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1239_, lean_object* v_constName_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1247_, v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1255_, lean_object* v_ref_1256_, lean_object* v_constName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1256_, v_constName_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_ref_1265_, lean_object* v_constName_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1264_, v_ref_1265_, v_constName_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v_ref_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1273_, lean_object* v_ref_1274_, lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1274_, v_msg_1275_, v_declHint_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_ref_1284_, lean_object* v_msg_1285_, lean_object* v_declHint_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1283_, v_ref_1284_, v_msg_1285_, v_declHint_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v_ref_1284_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1293_, lean_object* v_declHint_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1293_, v_declHint_1294_, v___y_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1301_, lean_object* v_declHint_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1301_, v_declHint_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1309_, lean_object* v_ref_1310_, lean_object* v_msg_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1310_, v_msg_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1318_, v_ref_1319_, v_msg_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v_ref_1319_);
return v_res_1326_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1333_, lean_object* v_idx_1334_, lean_object* v_e_1335_, lean_object* v_a_1336_, lean_object* v_00_u03b1_1337_, lean_object* v_x_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1345_ = l_Lean_mkProj(v_structName_1333_, v_idx_1334_, v_e_1335_);
v___x_1346_ = l_Lean_indentExpr(v___x_1345_);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_indentExpr(v_a_1336_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1351_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1353_, lean_object* v_idx_1354_, lean_object* v_e_1355_, lean_object* v_a_1356_, lean_object* v_00_u03b1_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1353_, v_idx_1354_, v_e_1355_, v_a_1356_, v_00_u03b1_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v_env_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_st_ref_get(v___y_1369_);
v_env_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_env_1372_);
lean_dec(v___x_1371_);
v___x_1373_ = 0;
lean_inc(v_constName_1365_);
v___x_1374_ = l_Lean_Environment_find_x3f(v_env_1372_, v_constName_1365_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_constName_1365_);
v_val_1376_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1374_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v___x_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 0);
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_val_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1391_, lean_object* v_structName_1392_, lean_object* v_e_1393_, lean_object* v_idx_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_a_1404_; uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_lt(v_a_1396_, v_upperBound_1391_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_idx_1394_);
lean_dec_ref(v_e_1393_);
lean_dec(v_structName_1392_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_b_1397_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; 
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
v___x_1410_ = lean_whnf(v_b_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
if (lean_obj_tag(v_a_1411_) == 7)
{
lean_object* v_body_1412_; uint8_t v___x_1413_; 
v_body_1412_ = lean_ctor_get(v_a_1411_, 2);
lean_inc_ref(v_body_1412_);
lean_dec_ref_known(v_a_1411_, 3);
v___x_1413_ = l_Lean_Expr_hasLooseBVars(v_body_1412_);
if (v___x_1413_ == 0)
{
v_a_1404_ = v_body_1412_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_inc_ref(v_e_1393_);
lean_inc(v_a_1396_);
lean_inc(v_structName_1392_);
v___x_1414_ = l_Lean_mkProj(v_structName_1392_, v_a_1396_, v_e_1393_);
v___x_1415_ = lean_expr_instantiate1(v_body_1412_, v___x_1414_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_body_1412_);
v_a_1404_ = v___x_1415_;
goto v___jp_1403_;
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1416_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1393_);
lean_inc(v_idx_1394_);
lean_inc(v_structName_1392_);
v___x_1417_ = l_Lean_mkProj(v_structName_1392_, v_idx_1394_, v_e_1393_);
v___x_1418_ = l_Lean_indentExpr(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1416_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
lean_inc_ref(v_a_1395_);
v___x_1422_ = l_Lean_indentExpr(v_a_1395_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1423_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_dec_ref_known(v___x_1424_, 1);
v_a_1404_ = v_a_1411_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_a_1411_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_idx_1394_);
lean_dec_ref(v_e_1393_);
lean_dec(v_structName_1392_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
else
{
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_idx_1394_);
lean_dec_ref(v_e_1393_);
lean_dec(v_structName_1392_);
return v___x_1410_;
}
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_add(v_a_1396_, v___x_1405_);
lean_dec(v_a_1396_);
v_a_1396_ = v___x_1406_;
v_b_1397_ = v_a_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1433_, lean_object* v_structName_1434_, lean_object* v_e_1435_, lean_object* v_idx_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1433_, v_structName_1434_, v_e_1435_, v_idx_1436_, v_a_1437_, v_a_1438_, v_b_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v_upperBound_1433_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1446_, lean_object* v_structName_1447_, lean_object* v_e_1448_, lean_object* v_idx_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_a_1459_; uint8_t v___x_1463_; 
v___x_1463_ = lean_nat_dec_lt(v_a_1451_, v_upperBound_1446_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_idx_1449_);
lean_dec_ref(v_e_1448_);
lean_dec(v_structName_1447_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1452_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; 
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
v___x_1465_ = lean_whnf(v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
if (lean_obj_tag(v_a_1466_) == 7)
{
lean_object* v_body_1467_; uint8_t v___x_1468_; 
v_body_1467_ = lean_ctor_get(v_a_1466_, 2);
lean_inc_ref(v_body_1467_);
lean_dec_ref_known(v_a_1466_, 3);
v___x_1468_ = l_Lean_Expr_hasLooseBVars(v_body_1467_);
if (v___x_1468_ == 0)
{
v_a_1459_ = v_body_1467_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc_ref(v_e_1448_);
lean_inc(v_a_1451_);
lean_inc(v_structName_1447_);
v___x_1469_ = l_Lean_mkProj(v_structName_1447_, v_a_1451_, v_e_1448_);
v___x_1470_ = lean_expr_instantiate1(v_body_1467_, v___x_1469_);
lean_dec_ref(v___x_1469_);
lean_dec_ref(v_body_1467_);
v_a_1459_ = v___x_1470_;
goto v___jp_1458_;
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1471_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1448_);
lean_inc(v_idx_1449_);
lean_inc(v_structName_1447_);
v___x_1472_ = l_Lean_mkProj(v_structName_1447_, v_idx_1449_, v_e_1448_);
v___x_1473_ = l_Lean_indentExpr(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
lean_inc_ref(v_a_1450_);
v___x_1477_ = l_Lean_indentExpr(v_a_1450_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1478_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec_ref_known(v___x_1479_, 1);
v_a_1459_ = v_a_1466_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_a_1466_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_idx_1449_);
lean_dec_ref(v_e_1448_);
lean_dec(v_structName_1447_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_idx_1449_);
lean_dec_ref(v_e_1448_);
lean_dec(v_structName_1447_);
return v___x_1465_;
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_add(v_a_1451_, v___x_1460_);
lean_dec(v_a_1451_);
v___x_1462_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1446_, v_structName_1447_, v_e_1448_, v_idx_1449_, v_a_1450_, v___x_1461_, v_a_1459_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1488_, lean_object* v_structName_1489_, lean_object* v_e_1490_, lean_object* v_idx_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1488_, v_structName_1489_, v_e_1490_, v_idx_1491_, v_a_1492_, v_a_1493_, v_b_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v_upperBound_1488_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1501_; lean_object* v_dummy_1502_; 
v___x_1501_ = lean_box(0);
v_dummy_1502_ = l_Lean_Expr_sort___override(v___x_1501_);
return v_dummy_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1503_, lean_object* v_idx_1504_, lean_object* v_e_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; 
lean_inc(v_a_1509_);
lean_inc_ref(v_a_1508_);
lean_inc(v_a_1507_);
lean_inc_ref(v_a_1506_);
lean_inc_ref(v_e_1505_);
v___x_1511_ = lean_infer_type(v_e_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
lean_inc(v_a_1509_);
lean_inc_ref(v_a_1508_);
lean_inc(v_a_1507_);
lean_inc_ref(v_a_1506_);
v___x_1513_ = lean_whnf(v_a_1512_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = l_Lean_Expr_getAppFn(v_a_1514_);
if (lean_obj_tag(v___x_1515_) == 4)
{
lean_object* v_declName_1516_; lean_object* v_us_1517_; lean_object* v___x_1518_; lean_object* v_env_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v_declName_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_declName_1516_);
v_us_1517_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_us_1517_);
lean_dec_ref_known(v___x_1515_, 2);
v___x_1518_ = lean_st_ref_get(v_a_1509_);
v_env_1522_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1522_);
lean_dec(v___x_1518_);
v___x_1523_ = 0;
v___x_1524_ = l_Lean_Environment_find_x3f(v_env_1522_, v_declName_1516_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v_us_1517_);
v___x_1525_ = lean_box(0);
v___x_1526_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1525_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; 
v_val_1527_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v___x_1524_, 1);
if (lean_obj_tag(v_val_1527_) == 5)
{
lean_object* v_val_1528_; lean_object* v_ctors_1529_; 
v_val_1528_ = lean_ctor_get(v_val_1527_, 0);
lean_inc_ref(v_val_1528_);
lean_dec_ref_known(v_val_1527_, 1);
v_ctors_1529_ = lean_ctor_get(v_val_1528_, 4);
lean_inc(v_ctors_1529_);
if (lean_obj_tag(v_ctors_1529_) == 1)
{
lean_object* v_tail_1530_; 
v_tail_1530_ = lean_ctor_get(v_ctors_1529_, 1);
if (lean_obj_tag(v_tail_1530_) == 0)
{
lean_object* v_toConstantVal_1531_; lean_object* v_numParams_1532_; lean_object* v_numIndices_1533_; lean_object* v_head_1534_; lean_object* v___x_1535_; 
v_toConstantVal_1531_ = lean_ctor_get(v_val_1528_, 0);
lean_inc_ref(v_toConstantVal_1531_);
v_numParams_1532_ = lean_ctor_get(v_val_1528_, 1);
lean_inc(v_numParams_1532_);
v_numIndices_1533_ = lean_ctor_get(v_val_1528_, 2);
lean_inc(v_numIndices_1533_);
lean_dec_ref(v_val_1528_);
v_head_1534_ = lean_ctor_get(v_ctors_1529_, 0);
lean_inc(v_head_1534_);
lean_dec_ref_known(v_ctors_1529_, 2);
v___x_1535_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1534_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
if (lean_obj_tag(v_a_1536_) == 6)
{
lean_object* v_val_1537_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v_name_1577_; uint8_t v___x_1578_; 
v_val_1537_ = lean_ctor_get(v_a_1536_, 0);
lean_inc_ref(v_val_1537_);
lean_dec_ref_known(v_a_1536_, 1);
v_name_1577_ = lean_ctor_get(v_toConstantVal_1531_, 0);
lean_inc(v_name_1577_);
lean_dec_ref(v_toConstantVal_1531_);
v___x_1578_ = lean_name_eq(v_name_1577_, v_structName_1503_);
lean_dec(v_name_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_val_1537_);
lean_dec(v_numIndices_1533_);
lean_dec(v_numParams_1532_);
lean_dec(v_us_1517_);
v___x_1579_ = lean_box(0);
v___x_1580_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1579_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
else
{
v___y_1539_ = v_a_1506_;
v___y_1540_ = v_a_1507_;
v___y_1541_ = v_a_1508_;
v___y_1542_ = v_a_1509_;
goto v___jp_1538_;
}
v___jp_1538_:
{
lean_object* v_dummy_1543_; lean_object* v_nargs_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_dummy_1543_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1544_ = l_Lean_Expr_getAppNumArgs(v_a_1514_);
lean_inc(v_nargs_1544_);
v___x_1545_ = lean_mk_array(v_nargs_1544_, v_dummy_1543_);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_sub(v_nargs_1544_, v___x_1546_);
lean_dec(v_nargs_1544_);
lean_inc(v_a_1514_);
v___x_1548_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1514_, v___x_1545_, v___x_1547_);
v___x_1549_ = lean_nat_add(v_numParams_1532_, v_numIndices_1533_);
lean_dec(v_numIndices_1533_);
v___x_1550_ = lean_array_get_size(v___x_1548_);
v___x_1551_ = lean_nat_dec_eq(v___x_1549_, v___x_1550_);
lean_dec(v___x_1549_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_val_1537_);
lean_dec(v_numParams_1532_);
lean_dec(v_us_1517_);
v___x_1552_ = lean_box(0);
v___x_1553_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1552_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1553_;
}
else
{
lean_object* v_toConstantVal_1554_; lean_object* v_name_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_toConstantVal_1554_ = lean_ctor_get(v_val_1537_, 0);
lean_inc_ref(v_toConstantVal_1554_);
lean_dec_ref(v_val_1537_);
v_name_1555_ = lean_ctor_get(v_toConstantVal_1554_, 0);
lean_inc(v_name_1555_);
lean_dec_ref(v_toConstantVal_1554_);
v___x_1556_ = l_Lean_mkConst(v_name_1555_, v_us_1517_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = l_Array_toSubarray___redArg(v___x_1548_, v___x_1557_, v_numParams_1532_);
v___x_1559_ = l_Subarray_copy___redArg(v___x_1558_);
v___x_1560_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1556_, v___x_1559_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
lean_inc(v_a_1514_);
lean_inc_ref(v_e_1505_);
lean_inc(v_structName_1503_);
lean_inc(v_idx_1504_);
v___x_1562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1504_, v_structName_1503_, v_e_1505_, v_idx_1504_, v_a_1514_, v___x_1557_, v_a_1561_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
v___x_1564_ = lean_whnf(v_a_1563_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1576_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_a_1565_) == 7)
{
lean_object* v_binderType_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_dec(v_a_1514_);
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
v_binderType_1569_ = lean_ctor_get(v_a_1565_, 1);
lean_inc_ref(v_binderType_1569_);
lean_dec_ref_known(v_a_1565_, 3);
v___x_1570_ = lean_expr_consume_type_annotations(v_binderType_1569_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1570_);
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1567_);
lean_dec(v_a_1565_);
v___x_1574_ = lean_box(0);
v___x_1575_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1574_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1575_;
}
}
}
else
{
lean_dec(v_a_1514_);
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
return v___x_1564_;
}
}
else
{
lean_dec(v_a_1514_);
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
return v___x_1562_;
}
}
else
{
lean_dec(v_a_1514_);
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
return v___x_1560_;
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_a_1536_);
lean_dec(v_numIndices_1533_);
lean_dec(v_numParams_1532_);
lean_dec_ref(v_toConstantVal_1531_);
lean_dec(v_us_1517_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1589_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1590_;
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_numIndices_1533_);
lean_dec(v_numParams_1532_);
lean_dec_ref(v_toConstantVal_1531_);
lean_dec(v_us_1517_);
lean_dec(v_a_1514_);
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
v_a_1591_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1535_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1535_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1529_, 2);
lean_dec_ref(v_val_1528_);
lean_dec(v_us_1517_);
goto v___jp_1519_;
}
}
else
{
lean_dec(v_ctors_1529_);
lean_dec_ref(v_val_1528_);
lean_dec(v_us_1517_);
goto v___jp_1519_;
}
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v_val_1527_);
lean_dec(v_us_1517_);
v___x_1599_ = lean_box(0);
v___x_1600_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1599_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1600_;
}
}
v___jp_1519_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1520_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1521_;
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___x_1515_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1503_, v_idx_1504_, v_e_1505_, v_a_1514_, lean_box(0), v___x_1601_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1602_;
}
}
else
{
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
return v___x_1513_;
}
}
else
{
lean_dec_ref(v_e_1505_);
lean_dec(v_idx_1504_);
lean_dec(v_structName_1503_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1603_, lean_object* v_idx_1604_, lean_object* v_e_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1603_, v_idx_1604_, v_e_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1612_, lean_object* v_structName_1613_, lean_object* v_e_1614_, lean_object* v_idx_1615_, lean_object* v_a_1616_, lean_object* v_inst_1617_, lean_object* v_R_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v_c_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1612_, v_structName_1613_, v_e_1614_, v_idx_1615_, v_a_1616_, v_a_1619_, v_b_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1628_, lean_object* v_structName_1629_, lean_object* v_e_1630_, lean_object* v_idx_1631_, lean_object* v_a_1632_, lean_object* v_inst_1633_, lean_object* v_R_1634_, lean_object* v_a_1635_, lean_object* v_b_1636_, lean_object* v_c_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1628_, v_structName_1629_, v_e_1630_, v_idx_1631_, v_a_1632_, v_inst_1633_, v_R_1634_, v_a_1635_, v_b_1636_, v_c_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v_upperBound_1628_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1644_, lean_object* v_structName_1645_, lean_object* v_e_1646_, lean_object* v_idx_1647_, lean_object* v_a_1648_, lean_object* v_inst_1649_, lean_object* v_R_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_, lean_object* v_c_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1644_, v_structName_1645_, v_e_1646_, v_idx_1647_, v_a_1648_, v_a_1651_, v_b_1652_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1660_, lean_object* v_structName_1661_, lean_object* v_e_1662_, lean_object* v_idx_1663_, lean_object* v_a_1664_, lean_object* v_inst_1665_, lean_object* v_R_1666_, lean_object* v_a_1667_, lean_object* v_b_1668_, lean_object* v_c_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1660_, v_structName_1661_, v_e_1662_, v_idx_1663_, v_a_1664_, v_inst_1665_, v_R_1666_, v_a_1667_, v_b_1668_, v_c_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v_upperBound_1660_);
return v_res_1675_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1686_ = l_Lean_indentExpr(v_type_1679_);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1687_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1696_, lean_object* v_type_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_type_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1704_, v_type_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_ks_1716_; lean_object* v_vs_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1741_; 
v_ks_1716_ = lean_ctor_get(v_x_1712_, 0);
v_vs_1717_ = lean_ctor_get(v_x_1712_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_x_1712_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1719_ = v_x_1712_;
v_isShared_1720_ = v_isSharedCheck_1741_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_vs_1717_);
lean_inc(v_ks_1716_);
lean_dec(v_x_1712_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1741_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = lean_array_get_size(v_ks_1716_);
v___x_1722_ = lean_nat_dec_lt(v_x_1713_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec(v_x_1713_);
v___x_1723_ = lean_array_push(v_ks_1716_, v_x_1714_);
v___x_1724_ = lean_array_push(v_vs_1717_, v_x_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1724_);
lean_ctor_set(v___x_1719_, 0, v___x_1723_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
else
{
lean_object* v_k_x27_1728_; uint8_t v___x_1729_; 
v_k_x27_1728_ = lean_array_fget_borrowed(v_ks_1716_, v_x_1713_);
v___x_1729_ = l_Lean_instBEqMVarId_beq(v_x_1714_, v_k_x27_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1731_; 
if (v_isShared_1720_ == 0)
{
v___x_1731_ = v___x_1719_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_ks_1716_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_vs_1717_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_x_1713_, v___x_1732_);
lean_dec(v_x_1713_);
v_x_1712_ = v___x_1731_;
v_x_1713_ = v___x_1733_;
goto _start;
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = lean_array_fset(v_ks_1716_, v_x_1713_, v_x_1714_);
v___x_1737_ = lean_array_fset(v_vs_1717_, v_x_1713_, v_x_1715_);
lean_dec(v_x_1713_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1737_);
lean_ctor_set(v___x_1719_, 0, v___x_1736_);
v___x_1739_ = v___x_1719_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1742_, lean_object* v_k_1743_, lean_object* v_v_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1742_, v___x_1745_, v_k_1743_, v_v_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1748_, size_t v_x_1749_, size_t v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
lean_object* v_es_1753_; size_t v___x_1754_; size_t v___x_1755_; lean_object* v_j_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_es_1753_ = lean_ctor_get(v_x_1748_, 0);
v___x_1754_ = ((size_t)31ULL);
v___x_1755_ = lean_usize_land(v_x_1749_, v___x_1754_);
v_j_1756_ = lean_usize_to_nat(v___x_1755_);
v___x_1757_ = lean_array_get_size(v_es_1753_);
v___x_1758_ = lean_nat_dec_lt(v_j_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec(v_j_1756_);
lean_dec(v_x_1752_);
lean_dec(v_x_1751_);
return v_x_1748_;
}
else
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1797_; 
lean_inc_ref(v_es_1753_);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_x_1748_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v_x_1748_, 0);
lean_dec(v_unused_1798_);
v___x_1760_ = v_x_1748_;
v_isShared_1761_ = v_isSharedCheck_1797_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v_x_1748_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1797_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_v_1762_; lean_object* v___x_1763_; lean_object* v_xs_x27_1764_; lean_object* v___y_1766_; 
v_v_1762_ = lean_array_fget(v_es_1753_, v_j_1756_);
v___x_1763_ = lean_box(0);
v_xs_x27_1764_ = lean_array_fset(v_es_1753_, v_j_1756_, v___x_1763_);
switch(lean_obj_tag(v_v_1762_))
{
case 0:
{
lean_object* v_key_1771_; lean_object* v_val_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1782_; 
v_key_1771_ = lean_ctor_get(v_v_1762_, 0);
v_val_1772_ = lean_ctor_get(v_v_1762_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_v_1762_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1774_ = v_v_1762_;
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_val_1772_);
lean_inc(v_key_1771_);
lean_dec(v_v_1762_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
uint8_t v___x_1776_; 
v___x_1776_ = l_Lean_instBEqMVarId_beq(v_x_1751_, v_key_1771_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_del_object(v___x_1774_);
v___x_1777_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1771_, v_val_1772_, v_x_1751_, v_x_1752_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
v___y_1766_ = v___x_1778_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1780_; 
lean_dec(v_val_1772_);
lean_dec(v_key_1771_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_x_1752_);
lean_ctor_set(v___x_1774_, 0, v_x_1751_);
v___x_1780_ = v___x_1774_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_x_1751_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_x_1752_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
v___y_1766_ = v___x_1780_;
goto v___jp_1765_;
}
}
}
}
case 1:
{
lean_object* v_node_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1795_; 
v_node_1783_ = lean_ctor_get(v_v_1762_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_v_1762_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1785_ = v_v_1762_;
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_node_1783_);
lean_dec(v_v_1762_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
size_t v___x_1787_; size_t v___x_1788_; size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1787_ = ((size_t)5ULL);
v___x_1788_ = lean_usize_shift_right(v_x_1749_, v___x_1787_);
v___x_1789_ = ((size_t)1ULL);
v___x_1790_ = lean_usize_add(v_x_1750_, v___x_1789_);
v___x_1791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1783_, v___x_1788_, v___x_1790_, v_x_1751_, v_x_1752_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1791_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v___y_1766_ = v___x_1793_;
goto v___jp_1765_;
}
}
}
default: 
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_x_1751_);
lean_ctor_set(v___x_1796_, 1, v_x_1752_);
v___y_1766_ = v___x_1796_;
goto v___jp_1765_;
}
}
v___jp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_array_fset(v_xs_x27_1764_, v_j_1756_, v___y_1766_);
lean_dec(v_j_1756_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1767_);
v___x_1769_ = v___x_1760_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
lean_object* v_ks_1799_; lean_object* v_vs_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1818_; 
v_ks_1799_ = lean_ctor_get(v_x_1748_, 0);
v_vs_1800_ = lean_ctor_get(v_x_1748_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1748_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1802_ = v_x_1748_;
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_vs_1800_);
lean_inc(v_ks_1799_);
lean_dec(v_x_1748_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_ks_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_vs_1800_);
v___x_1805_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v_newNode_1806_; size_t v___x_1807_; uint8_t v___x_1808_; 
v_newNode_1806_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1805_, v_x_1751_, v_x_1752_);
v___x_1807_ = ((size_t)7ULL);
v___x_1808_ = lean_usize_dec_le(v___x_1807_, v_x_1750_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1806_);
v___x_1810_ = lean_unsigned_to_nat(4u);
v___x_1811_ = lean_nat_dec_lt(v___x_1809_, v___x_1810_);
lean_dec(v___x_1809_);
if (v___x_1811_ == 0)
{
lean_object* v_ks_1812_; lean_object* v_vs_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_ks_1812_ = lean_ctor_get(v_newNode_1806_, 0);
lean_inc_ref(v_ks_1812_);
v_vs_1813_ = lean_ctor_get(v_newNode_1806_, 1);
lean_inc_ref(v_vs_1813_);
lean_dec_ref(v_newNode_1806_);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1750_, v_ks_1812_, v_vs_1813_, v___x_1814_, v___x_1815_);
lean_dec_ref(v_vs_1813_);
lean_dec_ref(v_ks_1812_);
return v___x_1816_;
}
else
{
return v_newNode_1806_;
}
}
else
{
return v_newNode_1806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1819_, lean_object* v_keys_1820_, lean_object* v_vals_1821_, lean_object* v_i_1822_, lean_object* v_entries_1823_){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_array_get_size(v_keys_1820_);
v___x_1825_ = lean_nat_dec_lt(v_i_1822_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec(v_i_1822_);
return v_entries_1823_;
}
else
{
lean_object* v_k_1826_; lean_object* v_v_1827_; uint64_t v___x_1828_; size_t v_h_1829_; size_t v___x_1830_; lean_object* v___x_1831_; size_t v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; size_t v_h_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_k_1826_ = lean_array_fget_borrowed(v_keys_1820_, v_i_1822_);
v_v_1827_ = lean_array_fget_borrowed(v_vals_1821_, v_i_1822_);
v___x_1828_ = l_Lean_instHashableMVarId_hash(v_k_1826_);
v_h_1829_ = lean_uint64_to_usize(v___x_1828_);
v___x_1830_ = ((size_t)5ULL);
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_sub(v_depth_1819_, v___x_1832_);
v___x_1834_ = lean_usize_mul(v___x_1830_, v___x_1833_);
v_h_1835_ = lean_usize_shift_right(v_h_1829_, v___x_1834_);
v___x_1836_ = lean_nat_add(v_i_1822_, v___x_1831_);
lean_dec(v_i_1822_);
lean_inc(v_v_1827_);
lean_inc(v_k_1826_);
v___x_1837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1823_, v_h_1835_, v_depth_1819_, v_k_1826_, v_v_1827_);
v_i_1822_ = v___x_1836_;
v_entries_1823_ = v___x_1837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1839_, lean_object* v_keys_1840_, lean_object* v_vals_1841_, lean_object* v_i_1842_, lean_object* v_entries_1843_){
_start:
{
size_t v_depth_boxed_1844_; lean_object* v_res_1845_; 
v_depth_boxed_1844_ = lean_unbox_usize(v_depth_1839_);
lean_dec(v_depth_1839_);
v_res_1845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1844_, v_keys_1840_, v_vals_1841_, v_i_1842_, v_entries_1843_);
lean_dec_ref(v_vals_1841_);
lean_dec_ref(v_keys_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
size_t v_x_1146__boxed_1851_; size_t v_x_1147__boxed_1852_; lean_object* v_res_1853_; 
v_x_1146__boxed_1851_ = lean_unbox_usize(v_x_1847_);
lean_dec(v_x_1847_);
v_x_1147__boxed_1852_ = lean_unbox_usize(v_x_1848_);
lean_dec(v_x_1848_);
v_res_1853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1846_, v_x_1146__boxed_1851_, v_x_1147__boxed_1852_, v_x_1849_, v_x_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
uint64_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = l_Lean_instHashableMVarId_hash(v_x_1855_);
v___x_1858_ = lean_uint64_to_usize(v___x_1857_);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1854_, v___x_1858_, v___x_1859_, v_x_1855_, v_x_1856_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1861_, lean_object* v_val_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_mctx_1866_; lean_object* v_cache_1867_; lean_object* v_zetaDeltaFVarIds_1868_; lean_object* v_postponed_1869_; lean_object* v_diag_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1899_; 
v___x_1865_ = lean_st_ref_take(v___y_1863_);
v_mctx_1866_ = lean_ctor_get(v___x_1865_, 0);
v_cache_1867_ = lean_ctor_get(v___x_1865_, 1);
v_zetaDeltaFVarIds_1868_ = lean_ctor_get(v___x_1865_, 2);
v_postponed_1869_ = lean_ctor_get(v___x_1865_, 3);
v_diag_1870_ = lean_ctor_get(v___x_1865_, 4);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1872_ = v___x_1865_;
v_isShared_1873_ = v_isSharedCheck_1899_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_diag_1870_);
lean_inc(v_postponed_1869_);
lean_inc(v_zetaDeltaFVarIds_1868_);
lean_inc(v_cache_1867_);
lean_inc(v_mctx_1866_);
lean_dec(v___x_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1899_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_depth_1874_; lean_object* v_levelAssignDepth_1875_; lean_object* v_lmvarCounter_1876_; lean_object* v_mvarCounter_1877_; lean_object* v_lDecls_1878_; lean_object* v_decls_1879_; lean_object* v_userNames_1880_; lean_object* v_lAssignment_1881_; lean_object* v_eAssignment_1882_; lean_object* v_dAssignment_1883_; lean_object* v_instanceTypedMVars_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1898_; 
v_depth_1874_ = lean_ctor_get(v_mctx_1866_, 0);
v_levelAssignDepth_1875_ = lean_ctor_get(v_mctx_1866_, 1);
v_lmvarCounter_1876_ = lean_ctor_get(v_mctx_1866_, 2);
v_mvarCounter_1877_ = lean_ctor_get(v_mctx_1866_, 3);
v_lDecls_1878_ = lean_ctor_get(v_mctx_1866_, 4);
v_decls_1879_ = lean_ctor_get(v_mctx_1866_, 5);
v_userNames_1880_ = lean_ctor_get(v_mctx_1866_, 6);
v_lAssignment_1881_ = lean_ctor_get(v_mctx_1866_, 7);
v_eAssignment_1882_ = lean_ctor_get(v_mctx_1866_, 8);
v_dAssignment_1883_ = lean_ctor_get(v_mctx_1866_, 9);
v_instanceTypedMVars_1884_ = lean_ctor_get(v_mctx_1866_, 10);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_mctx_1866_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1886_ = v_mctx_1866_;
v_isShared_1887_ = v_isSharedCheck_1898_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_instanceTypedMVars_1884_);
lean_inc(v_dAssignment_1883_);
lean_inc(v_eAssignment_1882_);
lean_inc(v_lAssignment_1881_);
lean_inc(v_userNames_1880_);
lean_inc(v_decls_1879_);
lean_inc(v_lDecls_1878_);
lean_inc(v_mvarCounter_1877_);
lean_inc(v_lmvarCounter_1876_);
lean_inc(v_levelAssignDepth_1875_);
lean_inc(v_depth_1874_);
lean_dec(v_mctx_1866_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1898_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1882_, v_mvarId_1861_, v_val_1862_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 8, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_depth_1874_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_levelAssignDepth_1875_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_lmvarCounter_1876_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_mvarCounter_1877_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_lDecls_1878_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v_decls_1879_);
lean_ctor_set(v_reuseFailAlloc_1897_, 6, v_userNames_1880_);
lean_ctor_set(v_reuseFailAlloc_1897_, 7, v_lAssignment_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_dAssignment_1883_);
lean_ctor_set(v_reuseFailAlloc_1897_, 10, v_instanceTypedMVars_1884_);
v___x_1890_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1890_);
v___x_1892_ = v___x_1872_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_cache_1867_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_zetaDeltaFVarIds_1868_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_postponed_1869_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_diag_1870_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_st_ref_put(v___y_1863_, v___x_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1900_, lean_object* v_val_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1900_, v_val_1901_, v___y_1902_);
lean_dec(v___y_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; 
lean_inc(v_a_1909_);
lean_inc_ref(v_a_1908_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc_ref(v_type_1905_);
v___x_1911_ = lean_infer_type(v_type_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_Meta_whnfD(v_a_1912_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1948_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1948_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1948_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
switch(lean_obj_tag(v_a_1914_))
{
case 3:
{
lean_object* v_u_1918_; lean_object* v___x_1920_; 
lean_dec_ref(v_type_1905_);
v_u_1918_ = lean_ctor_get(v_a_1914_, 0);
lean_inc(v_u_1918_);
lean_dec_ref_known(v_a_1914_, 1);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v_u_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_u_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
case 2:
{
lean_object* v_mvarId_1922_; lean_object* v___x_1923_; 
lean_del_object(v___x_1916_);
v_mvarId_1922_ = lean_ctor_get(v_a_1914_, 0);
lean_inc_n(v_mvarId_1922_, 2);
lean_dec_ref_known(v_a_1914_, 1);
v___x_1923_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1922_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; uint8_t v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = lean_unbox(v_a_1924_);
lean_dec(v_a_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v_type_1905_);
v___x_1926_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_n(v_a_1927_, 2);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = l_Lean_mkSort(v_a_1927_);
v___x_1929_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1922_, v___x_1928_, v_a_1907_);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1929_, 0);
lean_dec(v_unused_1937_);
v___x_1931_ = v___x_1929_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v___x_1929_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_a_1927_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1927_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_dec(v_mvarId_1922_);
return v___x_1926_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_mvarId_1922_);
v___x_1938_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1938_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_mvarId_1922_);
lean_dec_ref(v_type_1905_);
v_a_1939_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1923_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1923_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
default: 
{
lean_object* v___x_1947_; 
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
v___x_1947_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_type_1905_);
v_a_1949_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1913_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1913_);
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
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_type_1905_);
v_a_1957_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1911_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1911_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Meta_getLevel(v_type_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1972_, lean_object* v_val_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1972_, v_val_1973_, v___y_1975_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1980_, lean_object* v_val_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1980_, v_val_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1989_, v_x_1990_, v_x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1993_, lean_object* v_x_1994_, size_t v_x_1995_, size_t v_x_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1994_, v_x_1995_, v_x_1996_, v_x_1997_, v_x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_){
_start:
{
size_t v_x_1495__boxed_2006_; size_t v_x_1496__boxed_2007_; lean_object* v_res_2008_; 
v_x_1495__boxed_2006_ = lean_unbox_usize(v_x_2002_);
lean_dec(v_x_2002_);
v_x_1496__boxed_2007_ = lean_unbox_usize(v_x_2003_);
lean_dec(v_x_2003_);
v_res_2008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2000_, v_x_2001_, v_x_1495__boxed_2006_, v_x_1496__boxed_2007_, v_x_2004_, v_x_2005_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2009_, lean_object* v_n_2010_, lean_object* v_k_2011_, lean_object* v_v_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2010_, v_k_2011_, v_v_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2014_, size_t v_depth_2015_, lean_object* v_keys_2016_, lean_object* v_vals_2017_, lean_object* v_heq_2018_, lean_object* v_i_2019_, lean_object* v_entries_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2015_, v_keys_2016_, v_vals_2017_, v_i_2019_, v_entries_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2022_, lean_object* v_depth_2023_, lean_object* v_keys_2024_, lean_object* v_vals_2025_, lean_object* v_heq_2026_, lean_object* v_i_2027_, lean_object* v_entries_2028_){
_start:
{
size_t v_depth_boxed_2029_; lean_object* v_res_2030_; 
v_depth_boxed_2029_ = lean_unbox_usize(v_depth_2023_);
lean_dec(v_depth_2023_);
v_res_2030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2022_, v_depth_boxed_2029_, v_keys_2024_, v_vals_2025_, v_heq_2026_, v_i_2027_, v_entries_2028_);
lean_dec_ref(v_vals_2025_);
lean_dec_ref(v_keys_2024_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2032_, v_x_2033_, v_x_2034_, v_x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2037_, lean_object* v_b_2038_, lean_object* v_c_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
v___x_2045_ = lean_apply_7(v_k_2037_, v_b_2038_, v_c_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, lean_box(0));
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2046_, lean_object* v_b_2047_, lean_object* v_c_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2046_, v_b_2047_, v_c_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2055_, lean_object* v_k_2056_, uint8_t v_cleanupAnnotations_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___f_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2063_, 0, v_k_2056_);
v___x_2064_ = 0;
v___x_2065_ = lean_box(0);
v___x_2066_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2064_, v___x_2065_, v_type_2055_, v___f_2063_, v_cleanupAnnotations_2057_, v___x_2064_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2066_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2066_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2083_, lean_object* v_k_2084_, lean_object* v_cleanupAnnotations_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2091_; lean_object* v_res_2092_; 
v_cleanupAnnotations_boxed_2091_ = lean_unbox(v_cleanupAnnotations_2085_);
v_res_2092_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2083_, v_k_2084_, v_cleanupAnnotations_boxed_2091_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2093_, lean_object* v_type_2094_, lean_object* v_k_2095_, uint8_t v_cleanupAnnotations_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2094_, v_k_2095_, v_cleanupAnnotations_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_type_2104_, lean_object* v_k_2105_, lean_object* v_cleanupAnnotations_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2112_; lean_object* v_res_2113_; 
v_cleanupAnnotations_boxed_2112_ = lean_unbox(v_cleanupAnnotations_2106_);
v_res_2113_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2103_, v_type_2104_, v_k_2105_, v_cleanupAnnotations_boxed_2112_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2114_, size_t v_i_2115_, size_t v_stop_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_eq(v_i_2115_, v_stop_2116_);
if (v___x_2123_ == 0)
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = ((size_t)1ULL);
v___x_2125_ = lean_usize_sub(v_i_2115_, v___x_2124_);
v___x_2126_ = lean_array_uget_borrowed(v_as_2114_, v___x_2125_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___x_2126_);
v___x_2127_ = lean_infer_type(v___x_2126_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = l_Lean_Meta_getLevel(v_a_2128_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_mkLevelIMax_x27(v_a_2130_, v_b_2117_);
v_i_2115_ = v___x_2125_;
v_b_2117_ = v___x_2131_;
goto _start;
}
else
{
lean_dec(v_b_2117_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2129_, 1);
v_i_2115_ = v___x_2125_;
v_b_2117_ = v_a_2133_;
goto _start;
}
else
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v_b_2117_);
v_a_2135_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2127_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2127_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_b_2117_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2144_, lean_object* v_i_2145_, lean_object* v_stop_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
size_t v_i_boxed_2153_; size_t v_stop_boxed_2154_; lean_object* v_res_2155_; 
v_i_boxed_2153_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_stop_boxed_2154_ = lean_unbox_usize(v_stop_2146_);
lean_dec(v_stop_2146_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2144_, v_i_boxed_2153_, v_stop_boxed_2154_, v_b_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v_as_2144_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2156_, lean_object* v_e_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___y_2164_; lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_getLevel(v_e_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
v___x_2185_ = lean_array_get_size(v_xs_2156_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_nat_dec_lt(v___x_2186_, v___x_2185_);
if (v___x_2187_ == 0)
{
lean_dec(v_a_2184_);
v___y_2164_ = v___x_2183_;
goto v___jp_2163_;
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref_known(v___x_2183_, 1);
v___x_2188_ = lean_usize_of_nat(v___x_2185_);
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2156_, v___x_2188_, v___x_2189_, v_a_2184_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
v___y_2164_ = v___x_2190_;
goto v___jp_2163_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_a_2191_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2183_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2183_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
v___jp_2163_:
{
if (lean_obj_tag(v___y_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2174_; 
v_a_2165_ = lean_ctor_get(v___y_2164_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___y_2164_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2167_ = v___y_2164_;
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___y_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2169_ = l_Lean_Level_normalize(v_a_2165_);
lean_dec(v_a_2165_);
v___x_2170_ = l_Lean_mkSort(v___x_2169_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_a_2175_ = lean_ctor_get(v___y_2164_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___y_2164_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___y_2164_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___y_2164_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2199_, lean_object* v_e_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2199_, v_e_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_xs_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___f_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v___f_2214_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2215_ = 0;
v___x_2216_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2208_, v___f_2214_, v___x_2215_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2224_, lean_object* v_k_2225_, uint8_t v_cleanupAnnotations_2226_, uint8_t v_preserveNondepLet_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___f_2233_; uint8_t v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___f_2233_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2233_, 0, v_k_2225_);
v___x_2234_ = 1;
v___x_2235_ = 0;
v___x_2236_ = lean_box(0);
v___x_2237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2224_, v___x_2234_, v___x_2234_, v_preserveNondepLet_2227_, v___x_2235_, v___x_2236_, v___f_2233_, v_cleanupAnnotations_2226_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_a_2246_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2237_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2237_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2254_, lean_object* v_k_2255_, lean_object* v_cleanupAnnotations_2256_, lean_object* v_preserveNondepLet_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2263_; uint8_t v_preserveNondepLet_boxed_2264_; lean_object* v_res_2265_; 
v_cleanupAnnotations_boxed_2263_ = lean_unbox(v_cleanupAnnotations_2256_);
v_preserveNondepLet_boxed_2264_ = lean_unbox(v_preserveNondepLet_2257_);
v_res_2265_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2254_, v_k_2255_, v_cleanupAnnotations_boxed_2263_, v_preserveNondepLet_boxed_2264_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2266_, lean_object* v_e_2267_, lean_object* v_k_2268_, uint8_t v_cleanupAnnotations_2269_, uint8_t v_preserveNondepLet_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2267_, v_k_2268_, v_cleanupAnnotations_2269_, v_preserveNondepLet_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2277_, lean_object* v_e_2278_, lean_object* v_k_2279_, lean_object* v_cleanupAnnotations_2280_, lean_object* v_preserveNondepLet_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2287_; uint8_t v_preserveNondepLet_boxed_2288_; lean_object* v_res_2289_; 
v_cleanupAnnotations_boxed_2287_ = lean_unbox(v_cleanupAnnotations_2280_);
v_preserveNondepLet_boxed_2288_ = lean_unbox(v_preserveNondepLet_2281_);
v_res_2289_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2277_, v_e_2278_, v_k_2279_, v_cleanupAnnotations_boxed_2287_, v_preserveNondepLet_boxed_2288_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2290_, lean_object* v_e_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
lean_inc(v___y_2295_);
lean_inc_ref(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
v___x_2297_ = lean_infer_type(v_e_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = 0;
v___x_2300_ = 1;
v___x_2301_ = 1;
v___x_2302_ = l_Lean_Meta_mkForallFVars(v_xs_2290_, v_a_2298_, v___x_2299_, v___x_2300_, v___x_2299_, v___x_2301_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2302_;
}
else
{
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2303_, lean_object* v_e_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2303_, v_e_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v_xs_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___f_2318_; uint8_t v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; 
v___f_2318_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2319_ = 0;
v___x_2320_ = 1;
v___x_2321_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2312_, v___f_2318_, v___x_2319_, v___x_2320_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2341_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2342_ = l_Lean_MessageData_ofName(v_mvarId_2335_);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2345_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2354_, lean_object* v_mvarId_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2362_, lean_object* v_mvarId_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2362_, v_mvarId_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2376_; lean_object* v_mctx_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_st_ref_get(v_a_2372_);
v_mctx_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc_ref(v_mctx_2377_);
lean_dec(v___x_2376_);
v___x_2378_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2377_, v_mvarId_2370_);
lean_dec_ref(v_mctx_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_mvarId_2370_);
v_val_2380_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2382_ = v___x_2378_;
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v___x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2388_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_type_2384_; lean_object* v___x_2386_; 
v_type_2384_ = lean_ctor_get(v_val_2380_, 2);
lean_inc_ref(v_type_2384_);
lean_dec(v_val_2380_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
lean_ctor_set(v___x_2382_, 0, v_type_2384_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_type_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_lctx_2401_; lean_object* v___x_2402_; 
v_lctx_2401_ = lean_ctor_get(v_a_2397_, 2);
lean_inc(v_fvarId_2396_);
lean_inc_ref(v_lctx_2401_);
v___x_2402_ = lean_local_ctx_find(v_lctx_2401_, v_fvarId_2396_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2396_, v_a_2398_, v_a_2399_);
return v___x_2403_;
}
else
{
lean_object* v_val_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_fvarId_2396_);
v_val_2404_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2406_ = v___x_2402_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_val_2404_);
lean_dec(v___x_2402_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Lean_LocalDecl_type(v_val_2404_);
lean_dec(v_val_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2419_, v_a_2420_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
return v_res_2432_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_instMonadEIO(lean_box(0));
return v___x_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2435_ = l_StateRefT_x27_instMonad___redArg(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___f_2440_; 
v___x_2439_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2440_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2440_, 0, v___x_2439_);
return v___f_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___f_2442_; 
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2442_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2442_, 0, v___x_2441_);
return v___f_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; 
v___f_2443_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___f_2444_);
lean_ctor_set(v___x_2445_, 1, v___f_2443_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___f_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2447_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
return v___f_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___f_2449_; 
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2449_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2449_, 0, v___x_2448_);
return v___f_2449_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v___f_2450_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___f_2451_);
lean_ctor_set(v___x_2452_, 1, v___f_2450_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2455_, lean_object* v_inferType_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
uint8_t v_cacheInferType_2501_; 
v_cacheInferType_2501_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2501_ == 0)
{
lean_dec_ref(v_e_2455_);
goto v___jp_2462_;
}
else
{
uint8_t v___x_2502_; 
v___x_2502_ = l_Lean_Expr_hasMVar(v_e_2455_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2455_, v_a_2457_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2603_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2603_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2603_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v_cache_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2598_; 
v___x_2508_ = lean_st_ref_get(v_a_2458_);
v_cache_2509_ = lean_ctor_get(v___x_2508_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; 
v_unused_2599_ = lean_ctor_get(v___x_2508_, 4);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v___x_2508_, 3);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v___x_2508_, 2);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v___x_2508_, 0);
lean_dec(v_unused_2602_);
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2598_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_cache_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2598_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_inferType_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2556_; 
v_inferType_2513_ = lean_ctor_get(v_cache_2509_, 0);
lean_inc_ref(v_inferType_2513_);
lean_dec_ref(v_cache_2509_);
v___f_2514_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2515_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2504_);
v___x_2556_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2514_, v___x_2515_, v_inferType_2513_, v_a_2504_);
lean_dec_ref(v_inferType_2513_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v_toApplicative_2558_; lean_object* v_toFunctor_2559_; lean_object* v_toSeq_2560_; lean_object* v_toSeqLeft_2561_; lean_object* v_toSeqRight_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2572_; 
lean_del_object(v___x_2506_);
v___x_2557_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2558_ = lean_ctor_get(v___x_2557_, 0);
v_toFunctor_2559_ = lean_ctor_get(v_toApplicative_2558_, 0);
v_toSeq_2560_ = lean_ctor_get(v_toApplicative_2558_, 2);
v_toSeqLeft_2561_ = lean_ctor_get(v_toApplicative_2558_, 3);
v_toSeqRight_2562_ = lean_ctor_get(v_toApplicative_2558_, 4);
v___f_2563_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2564_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2559_, 2);
v___f_2565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2565_, 0, v_toFunctor_2559_);
v___f_2566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2566_, 0, v_toFunctor_2559_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___f_2565_);
lean_ctor_set(v___x_2567_, 1, v___f_2566_);
lean_inc(v_toSeqRight_2562_);
v___f_2568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2568_, 0, v_toSeqRight_2562_);
lean_inc(v_toSeqLeft_2561_);
v___f_2569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2569_, 0, v_toSeqLeft_2561_);
lean_inc(v_toSeq_2560_);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toSeq_2560_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v___f_2568_);
lean_ctor_set(v___x_2511_, 3, v___f_2569_);
lean_ctor_set(v___x_2511_, 2, v___f_2570_);
lean_ctor_set(v___x_2511_, 1, v___f_2563_);
lean_ctor_set(v___x_2511_, 0, v___x_2567_);
v___x_2572_ = v___x_2511_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___f_2563_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v___f_2570_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v___f_2569_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v___f_2568_);
v___x_2572_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_toCold_2579_; lean_object* v_cancelTk_x3f_2580_; 
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v___f_2564_);
v___x_2574_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2575_ = l_Lean_Core_instMonadRefCoreM;
v___x_2576_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2577_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2576_, v___x_2573_);
v___x_2578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2574_);
lean_ctor_set(v___x_2578_, 1, v___x_2575_);
lean_ctor_set(v___x_2578_, 2, v___x_2577_);
v_toCold_2579_ = lean_ctor_get(v_a_2459_, 0);
v_cancelTk_x3f_2580_ = lean_ctor_get(v_toCold_2579_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2580_) == 1)
{
lean_object* v_val_2581_; uint8_t v___x_2582_; 
v_val_2581_ = lean_ctor_get(v_cancelTk_x3f_2580_, 0);
v___x_2582_ = l_IO_CancelToken_isSet(v_val_2581_);
if (v___x_2582_ == 0)
{
lean_dec_ref_known(v___x_2578_, 3);
goto v___jp_2516_;
}
else
{
lean_object* v___x_1999__overap_2583_; lean_object* v___x_2584_; 
v___x_1999__overap_2583_ = l_Lean_throwInterruptException___redArg(v___x_2578_);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
v___x_2584_ = lean_apply_3(v___x_1999__overap_2583_, v_a_2459_, v_a_2460_, lean_box(0));
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2504_);
lean_dec_ref(v_inferType_2456_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2578_, 3);
goto v___jp_2516_;
}
}
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; 
lean_del_object(v___x_2511_);
lean_dec(v_a_2504_);
lean_dec_ref(v_inferType_2456_);
v_val_2594_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_val_2594_);
lean_dec_ref_known(v___x_2556_, 1);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v_val_2594_);
v___x_2596_ = v___x_2506_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_val_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
v___jp_2516_:
{
lean_object* v___x_2517_; 
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
v___x_2517_ = lean_apply_5(v_inferType_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, lean_box(0));
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; uint8_t v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
v___x_2519_ = l_Lean_Expr_hasMVar(v_a_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2554_; 
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2517_, 0);
lean_dec(v_unused_2555_);
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2554_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2517_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2554_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_cache_2524_; lean_object* v_mctx_2525_; lean_object* v_zetaDeltaFVarIds_2526_; lean_object* v_postponed_2527_; lean_object* v_diag_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2553_; 
v___x_2523_ = lean_st_ref_take(v_a_2458_);
v_cache_2524_ = lean_ctor_get(v___x_2523_, 1);
v_mctx_2525_ = lean_ctor_get(v___x_2523_, 0);
v_zetaDeltaFVarIds_2526_ = lean_ctor_get(v___x_2523_, 2);
v_postponed_2527_ = lean_ctor_get(v___x_2523_, 3);
v_diag_2528_ = lean_ctor_get(v___x_2523_, 4);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2553_;
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
v_isShared_2531_ = v_isSharedCheck_2553_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_inferType_2532_; lean_object* v_funInfo_2533_; lean_object* v_synthInstance_2534_; lean_object* v_whnf_2535_; lean_object* v_defEqTrans_2536_; lean_object* v_defEqPerm_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2552_; 
v_inferType_2532_ = lean_ctor_get(v_cache_2524_, 0);
v_funInfo_2533_ = lean_ctor_get(v_cache_2524_, 1);
v_synthInstance_2534_ = lean_ctor_get(v_cache_2524_, 2);
v_whnf_2535_ = lean_ctor_get(v_cache_2524_, 3);
v_defEqTrans_2536_ = lean_ctor_get(v_cache_2524_, 4);
v_defEqPerm_2537_ = lean_ctor_get(v_cache_2524_, 5);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_cache_2524_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2539_ = v_cache_2524_;
v_isShared_2540_ = v_isSharedCheck_2552_;
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
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_inc(v_a_2518_);
v___x_2541_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2514_, v___x_2515_, v_inferType_2532_, v_a_2504_, v_a_2518_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_funInfo_2533_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_synthInstance_2534_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_whnf_2535_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_defEqTrans_2536_);
lean_ctor_set(v_reuseFailAlloc_2551_, 5, v_defEqPerm_2537_);
v___x_2543_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2545_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2543_);
v___x_2545_ = v___x_2530_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_mctx_2525_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_zetaDeltaFVarIds_2526_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_postponed_2527_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_diag_2528_);
v___x_2545_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2546_ = lean_st_ref_put(v_a_2458_, v___x_2545_);
if (v_isShared_2522_ == 0)
{
v___x_2548_ = v___x_2521_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2518_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
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
lean_dec(v_a_2504_);
return v___x_2517_;
}
}
else
{
lean_dec(v_a_2504_);
return v___x_2517_;
}
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_inferType_2456_);
v_a_2604_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2503_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2503_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_dec_ref(v_e_2455_);
goto v___jp_2462_;
}
}
v___jp_2462_:
{
lean_object* v___x_2463_; lean_object* v_toApplicative_2464_; lean_object* v_toFunctor_2465_; lean_object* v_toSeq_2466_; lean_object* v_toSeqLeft_2467_; lean_object* v_toSeqRight_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_toCold_2484_; lean_object* v_cancelTk_x3f_2485_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2464_ = lean_ctor_get(v___x_2463_, 0);
v_toFunctor_2465_ = lean_ctor_get(v_toApplicative_2464_, 0);
v_toSeq_2466_ = lean_ctor_get(v_toApplicative_2464_, 2);
v_toSeqLeft_2467_ = lean_ctor_get(v_toApplicative_2464_, 3);
v_toSeqRight_2468_ = lean_ctor_get(v_toApplicative_2464_, 4);
v___f_2469_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2470_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2465_, 2);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toFunctor_2465_);
v___f_2472_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2472_, 0, v_toFunctor_2465_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___f_2471_);
lean_ctor_set(v___x_2473_, 1, v___f_2472_);
lean_inc(v_toSeqRight_2468_);
v___f_2474_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2474_, 0, v_toSeqRight_2468_);
lean_inc(v_toSeqLeft_2467_);
v___f_2475_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2475_, 0, v_toSeqLeft_2467_);
lean_inc(v_toSeq_2466_);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toSeq_2466_);
v___x_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2473_);
lean_ctor_set(v___x_2477_, 1, v___f_2469_);
lean_ctor_set(v___x_2477_, 2, v___f_2476_);
lean_ctor_set(v___x_2477_, 3, v___f_2475_);
lean_ctor_set(v___x_2477_, 4, v___f_2474_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___f_2470_);
v___x_2479_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2480_ = l_Lean_Core_instMonadRefCoreM;
v___x_2481_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2482_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2481_, v___x_2478_);
v___x_2483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2479_);
lean_ctor_set(v___x_2483_, 1, v___x_2480_);
lean_ctor_set(v___x_2483_, 2, v___x_2482_);
v_toCold_2484_ = lean_ctor_get(v_a_2459_, 0);
v_cancelTk_x3f_2485_ = lean_ctor_get(v_toCold_2484_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2485_) == 1)
{
lean_object* v_val_2486_; uint8_t v___x_2487_; 
v_val_2486_ = lean_ctor_get(v_cancelTk_x3f_2485_, 0);
v___x_2487_ = l_IO_CancelToken_isSet(v_val_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
lean_dec_ref_known(v___x_2483_, 3);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
v___x_2488_ = lean_apply_5(v_inferType_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, lean_box(0));
return v___x_2488_;
}
else
{
lean_object* v___x_1711__overap_2489_; lean_object* v___x_2490_; 
v___x_1711__overap_2489_ = l_Lean_throwInterruptException___redArg(v___x_2483_);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
v___x_2490_ = lean_apply_3(v___x_1711__overap_2489_, v_a_2459_, v_a_2460_, lean_box(0));
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref_known(v___x_2490_, 1);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
v___x_2491_ = lean_apply_5(v_inferType_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, lean_box(0));
return v___x_2491_;
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec_ref(v_inferType_2456_);
v_a_2492_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2490_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2490_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
else
{
lean_object* v___x_2500_; 
lean_dec_ref_known(v___x_2483_, 3);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
v___x_2500_ = lean_apply_5(v_inferType_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, lean_box(0));
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2612_, lean_object* v_inferType_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2612_, v_inferType_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2619_;
}
}
static lean_object* _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = 2;
v___x_2621_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2674_; uint8_t v_beta_2675_; 
v___x_2674_ = l_Lean_Meta_Context_config(v___y_2623_);
v_beta_2675_ = lean_ctor_get_uint8(v___x_2674_, 13);
if (v_beta_2675_ == 0)
{
lean_dec_ref(v___x_2674_);
goto v___jp_2628_;
}
else
{
uint8_t v_iota_2676_; 
v_iota_2676_ = lean_ctor_get_uint8(v___x_2674_, 12);
if (v_iota_2676_ == 0)
{
lean_dec_ref(v___x_2674_);
goto v___jp_2628_;
}
else
{
uint8_t v_zeta_2677_; 
v_zeta_2677_ = lean_ctor_get_uint8(v___x_2674_, 15);
if (v_zeta_2677_ == 0)
{
lean_dec_ref(v___x_2674_);
goto v___jp_2628_;
}
else
{
uint8_t v_zetaHave_2678_; 
v_zetaHave_2678_ = lean_ctor_get_uint8(v___x_2674_, 18);
if (v_zetaHave_2678_ == 0)
{
lean_dec_ref(v___x_2674_);
goto v___jp_2628_;
}
else
{
uint8_t v_zetaDelta_2679_; 
v_zetaDelta_2679_ = lean_ctor_get_uint8(v___x_2674_, 16);
if (v_zetaDelta_2679_ == 0)
{
lean_dec_ref(v___x_2674_);
goto v___jp_2628_;
}
else
{
uint8_t v_etaStruct_2680_; uint8_t v_proj_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_etaStruct_2680_ = lean_ctor_get_uint8(v___x_2674_, 10);
v_proj_2681_ = lean_ctor_get_uint8(v___x_2674_, 14);
lean_dec_ref(v___x_2674_);
v___x_2682_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2681_);
v___x_2683_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_2684_ = lean_nat_dec_eq(v___x_2682_, v___x_2683_);
lean_dec(v___x_2682_);
if (v___x_2684_ == 0)
{
goto v___jp_2628_;
}
else
{
uint8_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = 0;
v___x_2686_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2680_, v___x_2685_);
if (v___x_2686_ == 0)
{
goto v___jp_2628_;
}
else
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_apply_5(v_x_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2687_;
}
}
}
}
}
}
}
v___jp_2628_:
{
lean_object* v___x_2629_; uint8_t v_foApprox_2630_; uint8_t v_ctxApprox_2631_; uint8_t v_quasiPatternApprox_2632_; uint8_t v_constApprox_2633_; uint8_t v_isDefEqStuckEx_2634_; uint8_t v_unificationHints_2635_; uint8_t v_proofIrrelevance_2636_; uint8_t v_assignSyntheticOpaque_2637_; uint8_t v_offsetCnstrs_2638_; uint8_t v_transparency_2639_; uint8_t v_univApprox_2640_; uint8_t v_zetaUnused_2641_; uint8_t v_canUnfoldPredicateConfig_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2673_; 
v___x_2629_ = l_Lean_Meta_Context_config(v___y_2623_);
v_foApprox_2630_ = lean_ctor_get_uint8(v___x_2629_, 0);
v_ctxApprox_2631_ = lean_ctor_get_uint8(v___x_2629_, 1);
v_quasiPatternApprox_2632_ = lean_ctor_get_uint8(v___x_2629_, 2);
v_constApprox_2633_ = lean_ctor_get_uint8(v___x_2629_, 3);
v_isDefEqStuckEx_2634_ = lean_ctor_get_uint8(v___x_2629_, 4);
v_unificationHints_2635_ = lean_ctor_get_uint8(v___x_2629_, 5);
v_proofIrrelevance_2636_ = lean_ctor_get_uint8(v___x_2629_, 6);
v_assignSyntheticOpaque_2637_ = lean_ctor_get_uint8(v___x_2629_, 7);
v_offsetCnstrs_2638_ = lean_ctor_get_uint8(v___x_2629_, 8);
v_transparency_2639_ = lean_ctor_get_uint8(v___x_2629_, 9);
v_univApprox_2640_ = lean_ctor_get_uint8(v___x_2629_, 11);
v_zetaUnused_2641_ = lean_ctor_get_uint8(v___x_2629_, 17);
v_canUnfoldPredicateConfig_2642_ = lean_ctor_get_uint8(v___x_2629_, 19);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2644_ = v___x_2629_;
v_isShared_2645_ = v_isSharedCheck_2673_;
goto v_resetjp_2643_;
}
else
{
lean_dec(v___x_2629_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2673_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; uint8_t v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2650_; 
v___x_2646_ = 1;
v___x_2647_ = 0;
v___x_2648_ = 2;
if (v_isShared_2645_ == 0)
{
v___x_2650_ = v___x_2644_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 0, v_foApprox_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 1, v_ctxApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 2, v_quasiPatternApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 3, v_constApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 4, v_isDefEqStuckEx_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 5, v_unificationHints_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 6, v_proofIrrelevance_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 7, v_assignSyntheticOpaque_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 8, v_offsetCnstrs_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 9, v_transparency_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 11, v_univApprox_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 17, v_zetaUnused_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, 19, v_canUnfoldPredicateConfig_2642_);
v___x_2650_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
uint8_t v_trackZetaDelta_2651_; lean_object* v_zetaDeltaSet_2652_; lean_object* v_lctx_2653_; lean_object* v_localInstances_2654_; lean_object* v_defEqCtx_x3f_2655_; lean_object* v_synthPendingDepth_2656_; lean_object* v_customCanUnfoldPredicate_x3f_2657_; uint8_t v_univApprox_2658_; uint8_t v_inTypeClassResolution_2659_; uint8_t v_cacheInferType_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2670_; 
lean_ctor_set_uint8(v___x_2650_, 10, v___x_2647_);
lean_ctor_set_uint8(v___x_2650_, 12, v___x_2646_);
lean_ctor_set_uint8(v___x_2650_, 13, v___x_2646_);
lean_ctor_set_uint8(v___x_2650_, 14, v___x_2648_);
lean_ctor_set_uint8(v___x_2650_, 15, v___x_2646_);
lean_ctor_set_uint8(v___x_2650_, 16, v___x_2646_);
lean_ctor_set_uint8(v___x_2650_, 18, v___x_2646_);
v_trackZetaDelta_2651_ = lean_ctor_get_uint8(v___y_2623_, sizeof(void*)*7);
v_zetaDeltaSet_2652_ = lean_ctor_get(v___y_2623_, 1);
v_lctx_2653_ = lean_ctor_get(v___y_2623_, 2);
v_localInstances_2654_ = lean_ctor_get(v___y_2623_, 3);
v_defEqCtx_x3f_2655_ = lean_ctor_get(v___y_2623_, 4);
v_synthPendingDepth_2656_ = lean_ctor_get(v___y_2623_, 5);
v_customCanUnfoldPredicate_x3f_2657_ = lean_ctor_get(v___y_2623_, 6);
v_univApprox_2658_ = lean_ctor_get_uint8(v___y_2623_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2659_ = lean_ctor_get_uint8(v___y_2623_, sizeof(void*)*7 + 2);
v_cacheInferType_2660_ = lean_ctor_get_uint8(v___y_2623_, sizeof(void*)*7 + 3);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___y_2623_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___y_2623_, 0);
lean_dec(v_unused_2671_);
v___x_2662_ = v___y_2623_;
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2657_);
lean_inc(v_synthPendingDepth_2656_);
lean_inc(v_defEqCtx_x3f_2655_);
lean_inc(v_localInstances_2654_);
lean_inc(v_lctx_2653_);
lean_inc(v_zetaDeltaSet_2652_);
lean_dec(v___y_2623_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint64_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2650_);
v___x_2665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2665_, 0, v___x_2650_);
lean_ctor_set_uint64(v___x_2665_, sizeof(void*)*1, v___x_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_zetaDeltaSet_2652_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_lctx_2653_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_localInstances_2654_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v_defEqCtx_x3f_2655_);
lean_ctor_set(v_reuseFailAlloc_2669_, 5, v_synthPendingDepth_2656_);
lean_ctor_set(v_reuseFailAlloc_2669_, 6, v_customCanUnfoldPredicate_x3f_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2669_, sizeof(void*)*7, v_trackZetaDelta_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2669_, sizeof(void*)*7 + 1, v_univApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2669_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2669_, sizeof(void*)*7 + 3, v_cacheInferType_2660_);
v___x_2667_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_apply_5(v_x_2622_, v___x_2667_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
return v___x_2668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___y_2702_; lean_object* v___x_2719_; uint8_t v_transparency_2720_; uint8_t v___x_2721_; uint8_t v___x_2722_; 
v___x_2719_ = l_Lean_Meta_Context_config(v_a_2696_);
v_transparency_2720_ = lean_ctor_get_uint8(v___x_2719_, 9);
lean_dec_ref(v___x_2719_);
v___x_2721_ = 1;
v___x_2722_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_inc(v_a_2699_);
lean_inc_ref(v_a_2698_);
lean_inc(v_a_2697_);
lean_inc_ref(v_a_2696_);
v___x_2723_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
v___y_2702_ = v___x_2723_;
goto v___jp_2701_;
}
else
{
lean_object* v_keyedConfig_2724_; uint8_t v_trackZetaDelta_2725_; lean_object* v_zetaDeltaSet_2726_; lean_object* v_lctx_2727_; lean_object* v_localInstances_2728_; lean_object* v_defEqCtx_x3f_2729_; lean_object* v_synthPendingDepth_2730_; lean_object* v_customCanUnfoldPredicate_x3f_2731_; uint8_t v_univApprox_2732_; uint8_t v_inTypeClassResolution_2733_; uint8_t v_cacheInferType_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_keyedConfig_2724_ = lean_ctor_get(v_a_2696_, 0);
v_trackZetaDelta_2725_ = lean_ctor_get_uint8(v_a_2696_, sizeof(void*)*7);
v_zetaDeltaSet_2726_ = lean_ctor_get(v_a_2696_, 1);
v_lctx_2727_ = lean_ctor_get(v_a_2696_, 2);
v_localInstances_2728_ = lean_ctor_get(v_a_2696_, 3);
v_defEqCtx_x3f_2729_ = lean_ctor_get(v_a_2696_, 4);
v_synthPendingDepth_2730_ = lean_ctor_get(v_a_2696_, 5);
v_customCanUnfoldPredicate_x3f_2731_ = lean_ctor_get(v_a_2696_, 6);
v_univApprox_2732_ = lean_ctor_get_uint8(v_a_2696_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2733_ = lean_ctor_get_uint8(v_a_2696_, sizeof(void*)*7 + 2);
v_cacheInferType_2734_ = lean_ctor_get_uint8(v_a_2696_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2724_);
v___x_2735_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2721_, v_keyedConfig_2724_);
lean_inc(v_customCanUnfoldPredicate_x3f_2731_);
lean_inc(v_synthPendingDepth_2730_);
lean_inc(v_defEqCtx_x3f_2729_);
lean_inc_ref(v_localInstances_2728_);
lean_inc_ref(v_lctx_2727_);
lean_inc(v_zetaDeltaSet_2726_);
v___x_2736_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v_zetaDeltaSet_2726_);
lean_ctor_set(v___x_2736_, 2, v_lctx_2727_);
lean_ctor_set(v___x_2736_, 3, v_localInstances_2728_);
lean_ctor_set(v___x_2736_, 4, v_defEqCtx_x3f_2729_);
lean_ctor_set(v___x_2736_, 5, v_synthPendingDepth_2730_);
lean_ctor_set(v___x_2736_, 6, v_customCanUnfoldPredicate_x3f_2731_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7, v_trackZetaDelta_2725_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 1, v_univApprox_2732_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2733_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*7 + 3, v_cacheInferType_2734_);
lean_inc(v_a_2699_);
lean_inc_ref(v_a_2698_);
lean_inc(v_a_2697_);
v___x_2737_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2695_, v___x_2736_, v_a_2697_, v_a_2698_, v_a_2699_);
v___y_2702_ = v___x_2737_;
goto v___jp_2701_;
}
v___jp_2701_:
{
if (lean_obj_tag(v___y_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v___y_2702_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___y_2702_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___y_2702_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___y_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
v_a_2711_ = lean_ctor_get(v___y_2702_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___y_2702_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___y_2702_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___y_2702_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2745_, lean_object* v_x_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v___y_2753_; lean_object* v___x_2770_; uint8_t v_transparency_2771_; uint8_t v___x_2772_; uint8_t v___x_2773_; 
v___x_2770_ = l_Lean_Meta_Context_config(v_a_2747_);
v_transparency_2771_ = lean_ctor_get_uint8(v___x_2770_, 9);
lean_dec_ref(v___x_2770_);
v___x_2772_ = 1;
v___x_2773_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2771_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
lean_inc(v_a_2750_);
lean_inc_ref(v_a_2749_);
lean_inc(v_a_2748_);
lean_inc_ref(v_a_2747_);
v___x_2774_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
v___y_2753_ = v___x_2774_;
goto v___jp_2752_;
}
else
{
lean_object* v_keyedConfig_2775_; uint8_t v_trackZetaDelta_2776_; lean_object* v_zetaDeltaSet_2777_; lean_object* v_lctx_2778_; lean_object* v_localInstances_2779_; lean_object* v_defEqCtx_x3f_2780_; lean_object* v_synthPendingDepth_2781_; lean_object* v_customCanUnfoldPredicate_x3f_2782_; uint8_t v_univApprox_2783_; uint8_t v_inTypeClassResolution_2784_; uint8_t v_cacheInferType_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_keyedConfig_2775_ = lean_ctor_get(v_a_2747_, 0);
v_trackZetaDelta_2776_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*7);
v_zetaDeltaSet_2777_ = lean_ctor_get(v_a_2747_, 1);
v_lctx_2778_ = lean_ctor_get(v_a_2747_, 2);
v_localInstances_2779_ = lean_ctor_get(v_a_2747_, 3);
v_defEqCtx_x3f_2780_ = lean_ctor_get(v_a_2747_, 4);
v_synthPendingDepth_2781_ = lean_ctor_get(v_a_2747_, 5);
v_customCanUnfoldPredicate_x3f_2782_ = lean_ctor_get(v_a_2747_, 6);
v_univApprox_2783_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2784_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*7 + 2);
v_cacheInferType_2785_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2775_);
v___x_2786_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2772_, v_keyedConfig_2775_);
lean_inc(v_customCanUnfoldPredicate_x3f_2782_);
lean_inc(v_synthPendingDepth_2781_);
lean_inc(v_defEqCtx_x3f_2780_);
lean_inc_ref(v_localInstances_2779_);
lean_inc_ref(v_lctx_2778_);
lean_inc(v_zetaDeltaSet_2777_);
v___x_2787_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v_zetaDeltaSet_2777_);
lean_ctor_set(v___x_2787_, 2, v_lctx_2778_);
lean_ctor_set(v___x_2787_, 3, v_localInstances_2779_);
lean_ctor_set(v___x_2787_, 4, v_defEqCtx_x3f_2780_);
lean_ctor_set(v___x_2787_, 5, v_synthPendingDepth_2781_);
lean_ctor_set(v___x_2787_, 6, v_customCanUnfoldPredicate_x3f_2782_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*7, v_trackZetaDelta_2776_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*7 + 1, v_univApprox_2783_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2784_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*7 + 3, v_cacheInferType_2785_);
lean_inc(v_a_2750_);
lean_inc_ref(v_a_2749_);
lean_inc(v_a_2748_);
v___x_2788_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2746_, v___x_2787_, v_a_2748_, v_a_2749_, v_a_2750_);
v___y_2753_ = v___x_2788_;
goto v___jp_2752_;
}
v___jp_2752_:
{
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v_a_2754_ = lean_ctor_get(v___y_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___y_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___y_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___y_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___y_2753_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___y_2753_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___y_2753_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___y_2753_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_x_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2789_, v_x_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
return v_res_2796_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = l_Lean_interruptExceptionId;
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
lean_object* v_ks_2819_; lean_object* v_vs_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2849_; 
v_ks_2819_ = lean_ctor_get(v_x_2815_, 0);
v_vs_2820_ = lean_ctor_get(v_x_2815_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2815_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2822_ = v_x_2815_;
v_isShared_2823_ = v_isSharedCheck_2849_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_vs_2820_);
lean_inc(v_ks_2819_);
lean_dec(v_x_2815_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2849_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint8_t v___y_2825_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = lean_array_get_size(v_ks_2819_);
v___x_2838_ = lean_nat_dec_lt(v_x_2816_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2822_);
lean_dec(v_x_2816_);
v___x_2839_ = lean_array_push(v_ks_2819_, v_x_2817_);
v___x_2840_ = lean_array_push(v_vs_2820_, v_x_2818_);
v___x_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
return v___x_2841_;
}
else
{
lean_object* v_expr_2842_; uint64_t v_configKey_2843_; lean_object* v_k_x27_2844_; lean_object* v_expr_2845_; uint64_t v_configKey_2846_; uint8_t v___x_2847_; 
v_expr_2842_ = lean_ctor_get(v_x_2817_, 0);
v_configKey_2843_ = lean_ctor_get_uint64(v_x_2817_, sizeof(void*)*1);
v_k_x27_2844_ = lean_array_fget_borrowed(v_ks_2819_, v_x_2816_);
v_expr_2845_ = lean_ctor_get(v_k_x27_2844_, 0);
v_configKey_2846_ = lean_ctor_get_uint64(v_k_x27_2844_, sizeof(void*)*1);
v___x_2847_ = lean_expr_equal(v_expr_2842_, v_expr_2845_);
if (v___x_2847_ == 0)
{
v___y_2825_ = v___x_2847_;
goto v___jp_2824_;
}
else
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_uint64_dec_eq(v_configKey_2843_, v_configKey_2846_);
v___y_2825_ = v___x_2848_;
goto v___jp_2824_;
}
}
v___jp_2824_:
{
if (v___y_2825_ == 0)
{
lean_object* v___x_2827_; 
if (v_isShared_2823_ == 0)
{
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_ks_2819_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_vs_2820_);
v___x_2827_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_add(v_x_2816_, v___x_2828_);
lean_dec(v_x_2816_);
v_x_2815_ = v___x_2827_;
v_x_2816_ = v___x_2829_;
goto _start;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2832_ = lean_array_fset(v_ks_2819_, v_x_2816_, v_x_2817_);
v___x_2833_ = lean_array_fset(v_vs_2820_, v_x_2816_, v_x_2818_);
lean_dec(v_x_2816_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v___x_2833_);
lean_ctor_set(v___x_2822_, 0, v___x_2832_);
v___x_2835_ = v___x_2822_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2850_, lean_object* v_k_2851_, lean_object* v_v_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2850_, v___x_2853_, v_k_2851_, v_v_2852_);
return v___x_2854_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2856_, size_t v_x_2857_, size_t v_x_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_){
_start:
{
if (lean_obj_tag(v_x_2856_) == 0)
{
lean_object* v_es_2861_; size_t v___x_2862_; size_t v___x_2863_; lean_object* v_j_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_es_2861_ = lean_ctor_get(v_x_2856_, 0);
v___x_2862_ = ((size_t)31ULL);
v___x_2863_ = lean_usize_land(v_x_2857_, v___x_2862_);
v_j_2864_ = lean_usize_to_nat(v___x_2863_);
v___x_2865_ = lean_array_get_size(v_es_2861_);
v___x_2866_ = lean_nat_dec_lt(v_j_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_dec(v_j_2864_);
lean_dec(v_x_2860_);
lean_dec_ref(v_x_2859_);
return v_x_2856_;
}
else
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2912_; 
lean_inc_ref(v_es_2861_);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_x_2856_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v_x_2856_, 0);
lean_dec(v_unused_2913_);
v___x_2868_ = v_x_2856_;
v_isShared_2869_ = v_isSharedCheck_2912_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_x_2856_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2912_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_v_2870_; lean_object* v___x_2871_; lean_object* v_xs_x27_2872_; lean_object* v___y_2874_; 
v_v_2870_ = lean_array_fget(v_es_2861_, v_j_2864_);
v___x_2871_ = lean_box(0);
v_xs_x27_2872_ = lean_array_fset(v_es_2861_, v_j_2864_, v___x_2871_);
switch(lean_obj_tag(v_v_2870_))
{
case 0:
{
lean_object* v_key_2879_; lean_object* v_val_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2897_; 
v_key_2879_ = lean_ctor_get(v_v_2870_, 0);
v_val_2880_ = lean_ctor_get(v_v_2870_, 1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_v_2870_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2882_ = v_v_2870_;
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_val_2880_);
lean_inc(v_key_2879_);
lean_dec(v_v_2870_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2897_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
uint8_t v___y_2885_; lean_object* v_expr_2891_; uint64_t v_configKey_2892_; lean_object* v_expr_2893_; uint64_t v_configKey_2894_; uint8_t v___x_2895_; 
v_expr_2891_ = lean_ctor_get(v_x_2859_, 0);
v_configKey_2892_ = lean_ctor_get_uint64(v_x_2859_, sizeof(void*)*1);
v_expr_2893_ = lean_ctor_get(v_key_2879_, 0);
v_configKey_2894_ = lean_ctor_get_uint64(v_key_2879_, sizeof(void*)*1);
v___x_2895_ = lean_expr_equal(v_expr_2891_, v_expr_2893_);
if (v___x_2895_ == 0)
{
v___y_2885_ = v___x_2895_;
goto v___jp_2884_;
}
else
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_uint64_dec_eq(v_configKey_2892_, v_configKey_2894_);
v___y_2885_ = v___x_2896_;
goto v___jp_2884_;
}
v___jp_2884_:
{
if (v___y_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_del_object(v___x_2882_);
v___x_2886_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2879_, v_val_2880_, v_x_2859_, v_x_2860_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
v___y_2874_ = v___x_2887_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2889_; 
lean_dec(v_val_2880_);
lean_dec(v_key_2879_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v_x_2860_);
lean_ctor_set(v___x_2882_, 0, v_x_2859_);
v___x_2889_ = v___x_2882_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_x_2859_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_x_2860_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v___y_2874_ = v___x_2889_;
goto v___jp_2873_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2910_; 
v_node_2898_ = lean_ctor_get(v_v_2870_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_v_2870_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2900_ = v_v_2870_;
v_isShared_2901_ = v_isSharedCheck_2910_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_node_2898_);
lean_dec(v_v_2870_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2910_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
size_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2902_ = ((size_t)5ULL);
v___x_2903_ = lean_usize_shift_right(v_x_2857_, v___x_2902_);
v___x_2904_ = ((size_t)1ULL);
v___x_2905_ = lean_usize_add(v_x_2858_, v___x_2904_);
v___x_2906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2898_, v___x_2903_, v___x_2905_, v_x_2859_, v_x_2860_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2906_);
v___x_2908_ = v___x_2900_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
v___y_2874_ = v___x_2908_;
goto v___jp_2873_;
}
}
}
default: 
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_x_2859_);
lean_ctor_set(v___x_2911_, 1, v_x_2860_);
v___y_2874_ = v___x_2911_;
goto v___jp_2873_;
}
}
v___jp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2875_ = lean_array_fset(v_xs_x27_2872_, v_j_2864_, v___y_2874_);
lean_dec(v_j_2864_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2875_);
v___x_2877_ = v___x_2868_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
else
{
lean_object* v_ks_2914_; lean_object* v_vs_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2933_; 
v_ks_2914_ = lean_ctor_get(v_x_2856_, 0);
v_vs_2915_ = lean_ctor_get(v_x_2856_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_x_2856_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2917_ = v_x_2856_;
v_isShared_2918_ = v_isSharedCheck_2933_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_vs_2915_);
lean_inc(v_ks_2914_);
lean_dec(v_x_2856_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2933_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_ks_2914_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_vs_2915_);
v___x_2920_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v_newNode_2921_; size_t v___x_2922_; uint8_t v___x_2923_; 
v_newNode_2921_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2920_, v_x_2859_, v_x_2860_);
v___x_2922_ = ((size_t)7ULL);
v___x_2923_ = lean_usize_dec_le(v___x_2922_, v_x_2858_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2921_);
v___x_2925_ = lean_unsigned_to_nat(4u);
v___x_2926_ = lean_nat_dec_lt(v___x_2924_, v___x_2925_);
lean_dec(v___x_2924_);
if (v___x_2926_ == 0)
{
lean_object* v_ks_2927_; lean_object* v_vs_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_ks_2927_ = lean_ctor_get(v_newNode_2921_, 0);
lean_inc_ref(v_ks_2927_);
v_vs_2928_ = lean_ctor_get(v_newNode_2921_, 1);
lean_inc_ref(v_vs_2928_);
lean_dec_ref(v_newNode_2921_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2931_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2858_, v_ks_2927_, v_vs_2928_, v___x_2929_, v___x_2930_);
lean_dec_ref(v_vs_2928_);
lean_dec_ref(v_ks_2927_);
return v___x_2931_;
}
else
{
return v_newNode_2921_;
}
}
else
{
return v_newNode_2921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2934_, lean_object* v_keys_2935_, lean_object* v_vals_2936_, lean_object* v_i_2937_, lean_object* v_entries_2938_){
_start:
{
lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = lean_array_get_size(v_keys_2935_);
v___x_2940_ = lean_nat_dec_lt(v_i_2937_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_dec(v_i_2937_);
return v_entries_2938_;
}
else
{
lean_object* v_k_2941_; lean_object* v_expr_2942_; uint64_t v_configKey_2943_; lean_object* v_v_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; size_t v_h_2947_; size_t v___x_2948_; lean_object* v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v_h_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_k_2941_ = lean_array_fget_borrowed(v_keys_2935_, v_i_2937_);
v_expr_2942_ = lean_ctor_get(v_k_2941_, 0);
v_configKey_2943_ = lean_ctor_get_uint64(v_k_2941_, sizeof(void*)*1);
v_v_2944_ = lean_array_fget_borrowed(v_vals_2936_, v_i_2937_);
v___x_2945_ = l_Lean_Expr_hash(v_expr_2942_);
v___x_2946_ = lean_uint64_mix_hash(v___x_2945_, v_configKey_2943_);
v_h_2947_ = lean_uint64_to_usize(v___x_2946_);
v___x_2948_ = ((size_t)5ULL);
v___x_2949_ = lean_unsigned_to_nat(1u);
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_sub(v_depth_2934_, v___x_2950_);
v___x_2952_ = lean_usize_mul(v___x_2948_, v___x_2951_);
v_h_2953_ = lean_usize_shift_right(v_h_2947_, v___x_2952_);
v___x_2954_ = lean_nat_add(v_i_2937_, v___x_2949_);
lean_dec(v_i_2937_);
lean_inc(v_v_2944_);
lean_inc(v_k_2941_);
v___x_2955_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2938_, v_h_2953_, v_depth_2934_, v_k_2941_, v_v_2944_);
v_i_2937_ = v___x_2954_;
v_entries_2938_ = v___x_2955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2957_, lean_object* v_keys_2958_, lean_object* v_vals_2959_, lean_object* v_i_2960_, lean_object* v_entries_2961_){
_start:
{
size_t v_depth_boxed_2962_; lean_object* v_res_2963_; 
v_depth_boxed_2962_ = lean_unbox_usize(v_depth_2957_);
lean_dec(v_depth_2957_);
v_res_2963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2962_, v_keys_2958_, v_vals_2959_, v_i_2960_, v_entries_2961_);
lean_dec_ref(v_vals_2959_);
lean_dec_ref(v_keys_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
size_t v_x_2785__boxed_2969_; size_t v_x_2786__boxed_2970_; lean_object* v_res_2971_; 
v_x_2785__boxed_2969_ = lean_unbox_usize(v_x_2965_);
lean_dec(v_x_2965_);
v_x_2786__boxed_2970_ = lean_unbox_usize(v_x_2966_);
lean_dec(v_x_2966_);
v_res_2971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2964_, v_x_2785__boxed_2969_, v_x_2786__boxed_2970_, v_x_2967_, v_x_2968_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
lean_object* v_expr_2975_; uint64_t v_configKey_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v_expr_2975_ = lean_ctor_get(v_x_2973_, 0);
v_configKey_2976_ = lean_ctor_get_uint64(v_x_2973_, sizeof(void*)*1);
v___x_2977_ = l_Lean_Expr_hash(v_expr_2975_);
v___x_2978_ = lean_uint64_mix_hash(v___x_2977_, v_configKey_2976_);
v___x_2979_ = lean_uint64_to_usize(v___x_2978_);
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2972_, v___x_2979_, v___x_2980_, v_x_2973_, v_x_2974_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2982_, lean_object* v_vals_2983_, lean_object* v_i_2984_, lean_object* v_k_2985_){
_start:
{
uint8_t v___y_2987_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = lean_array_get_size(v_keys_2982_);
v___x_2994_ = lean_nat_dec_lt(v_i_2984_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
lean_dec(v_i_2984_);
v___x_2995_ = lean_box(0);
return v___x_2995_;
}
else
{
lean_object* v_expr_2996_; uint64_t v_configKey_2997_; lean_object* v_k_x27_2998_; lean_object* v_expr_2999_; uint64_t v_configKey_3000_; uint8_t v___x_3001_; 
v_expr_2996_ = lean_ctor_get(v_k_2985_, 0);
v_configKey_2997_ = lean_ctor_get_uint64(v_k_2985_, sizeof(void*)*1);
v_k_x27_2998_ = lean_array_fget_borrowed(v_keys_2982_, v_i_2984_);
v_expr_2999_ = lean_ctor_get(v_k_x27_2998_, 0);
v_configKey_3000_ = lean_ctor_get_uint64(v_k_x27_2998_, sizeof(void*)*1);
v___x_3001_ = lean_expr_equal(v_expr_2996_, v_expr_2999_);
if (v___x_3001_ == 0)
{
v___y_2987_ = v___x_3001_;
goto v___jp_2986_;
}
else
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_uint64_dec_eq(v_configKey_2997_, v_configKey_3000_);
v___y_2987_ = v___x_3002_;
goto v___jp_2986_;
}
}
v___jp_2986_:
{
if (v___y_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_nat_add(v_i_2984_, v___x_2988_);
lean_dec(v_i_2984_);
v_i_2984_ = v___x_2989_;
goto _start;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_array_fget_borrowed(v_vals_2983_, v_i_2984_);
lean_dec(v_i_2984_);
lean_inc(v___x_2991_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3003_, lean_object* v_vals_3004_, lean_object* v_i_3005_, lean_object* v_k_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3003_, v_vals_3004_, v_i_3005_, v_k_3006_);
lean_dec_ref(v_k_3006_);
lean_dec_ref(v_vals_3004_);
lean_dec_ref(v_keys_3003_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3008_, size_t v_x_3009_, lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3008_) == 0)
{
lean_object* v_es_3011_; lean_object* v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; lean_object* v_j_3015_; lean_object* v___x_3016_; 
v_es_3011_ = lean_ctor_get(v_x_3008_, 0);
v___x_3012_ = lean_box(2);
v___x_3013_ = ((size_t)31ULL);
v___x_3014_ = lean_usize_land(v_x_3009_, v___x_3013_);
v_j_3015_ = lean_usize_to_nat(v___x_3014_);
v___x_3016_ = lean_array_get_borrowed(v___x_3012_, v_es_3011_, v_j_3015_);
lean_dec(v_j_3015_);
switch(lean_obj_tag(v___x_3016_))
{
case 0:
{
lean_object* v_key_3017_; lean_object* v_val_3018_; uint8_t v___y_3020_; lean_object* v_expr_3023_; uint64_t v_configKey_3024_; lean_object* v_expr_3025_; uint64_t v_configKey_3026_; uint8_t v___x_3027_; 
v_key_3017_ = lean_ctor_get(v___x_3016_, 0);
v_val_3018_ = lean_ctor_get(v___x_3016_, 1);
v_expr_3023_ = lean_ctor_get(v_x_3010_, 0);
v_configKey_3024_ = lean_ctor_get_uint64(v_x_3010_, sizeof(void*)*1);
v_expr_3025_ = lean_ctor_get(v_key_3017_, 0);
v_configKey_3026_ = lean_ctor_get_uint64(v_key_3017_, sizeof(void*)*1);
v___x_3027_ = lean_expr_equal(v_expr_3023_, v_expr_3025_);
if (v___x_3027_ == 0)
{
v___y_3020_ = v___x_3027_;
goto v___jp_3019_;
}
else
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_uint64_dec_eq(v_configKey_3024_, v_configKey_3026_);
v___y_3020_ = v___x_3028_;
goto v___jp_3019_;
}
v___jp_3019_:
{
if (v___y_3020_ == 0)
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_box(0);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; 
lean_inc(v_val_3018_);
v___x_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_val_3018_);
return v___x_3022_;
}
}
}
case 1:
{
lean_object* v_node_3029_; size_t v___x_3030_; size_t v___x_3031_; 
v_node_3029_ = lean_ctor_get(v___x_3016_, 0);
v___x_3030_ = ((size_t)5ULL);
v___x_3031_ = lean_usize_shift_right(v_x_3009_, v___x_3030_);
v_x_3008_ = v_node_3029_;
v_x_3009_ = v___x_3031_;
goto _start;
}
default: 
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_box(0);
return v___x_3033_;
}
}
}
else
{
lean_object* v_ks_3034_; lean_object* v_vs_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_ks_3034_ = lean_ctor_get(v_x_3008_, 0);
v_vs_3035_ = lean_ctor_get(v_x_3008_, 1);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3034_, v_vs_3035_, v___x_3036_, v_x_3010_);
return v___x_3037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
size_t v_x_2990__boxed_3041_; lean_object* v_res_3042_; 
v_x_2990__boxed_3041_ = lean_unbox_usize(v_x_3039_);
lean_dec(v_x_3039_);
v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3038_, v_x_2990__boxed_3041_, v_x_3040_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3038_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v_expr_3045_; uint64_t v_configKey_3046_; uint64_t v___x_3047_; uint64_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v_expr_3045_ = lean_ctor_get(v_x_3044_, 0);
v_configKey_3046_ = lean_ctor_get_uint64(v_x_3044_, sizeof(void*)*1);
v___x_3047_ = l_Lean_Expr_hash(v_expr_3045_);
v___x_3048_ = lean_uint64_mix_hash(v___x_3047_, v_configKey_3046_);
v___x_3049_ = lean_uint64_to_usize(v___x_3048_);
v___x_3050_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3043_, v___x_3049_, v_x_3044_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3051_, v_x_3052_);
lean_dec_ref(v_x_3052_);
lean_dec_ref(v_x_3051_);
return v_res_3053_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
switch(lean_obj_tag(v_e_3057_))
{
case 0:
{
lean_object* v_deBruijnIndex_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_deBruijnIndex_3095_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_deBruijnIndex_3095_);
lean_dec_ref_known(v_e_3057_, 1);
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3097_ = l_Lean_mkBVar(v_deBruijnIndex_3095_);
v___x_3098_ = l_Lean_MessageData_ofExpr(v___x_3097_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3096_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3099_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3100_;
}
case 1:
{
lean_object* v_fvarId_3101_; lean_object* v___x_3102_; 
v_fvarId_3101_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_fvarId_3101_);
lean_dec_ref_known(v_e_3057_, 1);
v___x_3102_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3101_, v_a_3058_, v_a_3060_, v_a_3061_);
return v___x_3102_;
}
case 2:
{
lean_object* v_mvarId_3103_; lean_object* v___x_3104_; 
v_mvarId_3103_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_mvarId_3103_);
lean_dec_ref_known(v_e_3057_, 1);
v___x_3104_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3103_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3104_;
}
case 3:
{
lean_object* v_u_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_u_3105_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_u_3105_);
lean_dec_ref_known(v_e_3057_, 1);
v___x_3106_ = l_Lean_Level_succ___override(v_u_3105_);
v___x_3107_ = l_Lean_mkSort(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
case 4:
{
lean_object* v_declName_3109_; lean_object* v_us_3110_; 
v_declName_3109_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_declName_3109_);
v_us_3110_ = lean_ctor_get(v_e_3057_, 1);
lean_inc(v_us_3110_);
if (lean_obj_tag(v_us_3110_) == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref_known(v_e_3057_, 2);
v___x_3127_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3109_, v_us_3110_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3127_;
}
else
{
uint8_t v_cacheInferType_3128_; 
v_cacheInferType_3128_ = lean_ctor_get_uint8(v_a_3058_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3128_ == 0)
{
lean_dec_ref_known(v_e_3057_, 2);
goto v___jp_3111_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = l_Lean_Expr_hasMVar(v_e_3057_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3196_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3196_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3196_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3175_; lean_object* v_cache_3176_; lean_object* v_inferType_3177_; lean_object* v___x_3178_; 
v___x_3175_ = lean_st_ref_get(v_a_3059_);
v_cache_3176_ = lean_ctor_get(v___x_3175_, 1);
lean_inc_ref(v_cache_3176_);
lean_dec(v___x_3175_);
v_inferType_3177_ = lean_ctor_get(v_cache_3176_, 0);
lean_inc_ref(v_inferType_3177_);
lean_dec_ref(v_cache_3176_);
v___x_3178_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3177_, v_a_3131_);
lean_dec_ref(v_inferType_3177_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_toCold_3179_; lean_object* v_cancelTk_x3f_3180_; 
lean_del_object(v___x_3133_);
v_toCold_3179_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3180_ = lean_ctor_get(v_toCold_3179_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3180_) == 1)
{
lean_object* v_val_3181_; uint8_t v___x_3182_; 
v_val_3181_ = lean_ctor_get(v_cancelTk_x3f_3180_, 0);
v___x_3182_ = l_IO_CancelToken_isSet(v_val_3181_);
if (v___x_3182_ == 0)
{
goto v___jp_3135_;
}
else
{
lean_object* v___x_3183_; lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec(v_a_3131_);
lean_dec(v_us_3110_);
lean_dec(v_declName_3109_);
v___x_3183_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
goto v___jp_3135_;
}
}
else
{
lean_object* v_val_3192_; lean_object* v___x_3194_; 
lean_dec(v_a_3131_);
lean_dec(v_us_3110_);
lean_dec(v_declName_3109_);
v_val_3192_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v___x_3178_, 1);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_val_3192_);
v___x_3194_ = v___x_3133_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_val_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
v___jp_3135_:
{
lean_object* v___x_3136_; 
v___x_3136_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3109_, v_us_3110_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; uint8_t v___x_3138_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
v___x_3138_ = l_Lean_Expr_hasMVar(v_a_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3173_; 
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3136_, 0);
lean_dec(v_unused_3174_);
v___x_3140_ = v___x_3136_;
v_isShared_3141_ = v_isSharedCheck_3173_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v___x_3136_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3173_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v_cache_3143_; lean_object* v_mctx_3144_; lean_object* v_zetaDeltaFVarIds_3145_; lean_object* v_postponed_3146_; lean_object* v_diag_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3172_; 
v___x_3142_ = lean_st_ref_take(v_a_3059_);
v_cache_3143_ = lean_ctor_get(v___x_3142_, 1);
v_mctx_3144_ = lean_ctor_get(v___x_3142_, 0);
v_zetaDeltaFVarIds_3145_ = lean_ctor_get(v___x_3142_, 2);
v_postponed_3146_ = lean_ctor_get(v___x_3142_, 3);
v_diag_3147_ = lean_ctor_get(v___x_3142_, 4);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3149_ = v___x_3142_;
v_isShared_3150_ = v_isSharedCheck_3172_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_diag_3147_);
lean_inc(v_postponed_3146_);
lean_inc(v_zetaDeltaFVarIds_3145_);
lean_inc(v_cache_3143_);
lean_inc(v_mctx_3144_);
lean_dec(v___x_3142_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3172_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_inferType_3151_; lean_object* v_funInfo_3152_; lean_object* v_synthInstance_3153_; lean_object* v_whnf_3154_; lean_object* v_defEqTrans_3155_; lean_object* v_defEqPerm_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3171_; 
v_inferType_3151_ = lean_ctor_get(v_cache_3143_, 0);
v_funInfo_3152_ = lean_ctor_get(v_cache_3143_, 1);
v_synthInstance_3153_ = lean_ctor_get(v_cache_3143_, 2);
v_whnf_3154_ = lean_ctor_get(v_cache_3143_, 3);
v_defEqTrans_3155_ = lean_ctor_get(v_cache_3143_, 4);
v_defEqPerm_3156_ = lean_ctor_get(v_cache_3143_, 5);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_cache_3143_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3158_ = v_cache_3143_;
v_isShared_3159_ = v_isSharedCheck_3171_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_defEqPerm_3156_);
lean_inc(v_defEqTrans_3155_);
lean_inc(v_whnf_3154_);
lean_inc(v_synthInstance_3153_);
lean_inc(v_funInfo_3152_);
lean_inc(v_inferType_3151_);
lean_dec(v_cache_3143_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3171_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
lean_inc(v_a_3137_);
v___x_3160_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3151_, v_a_3131_, v_a_3137_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 0, v___x_3160_);
v___x_3162_ = v___x_3158_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_funInfo_3152_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_synthInstance_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_whnf_3154_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_defEqTrans_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v_defEqPerm_3156_);
v___x_3162_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3164_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3162_);
v___x_3164_ = v___x_3149_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_mctx_3144_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_zetaDeltaFVarIds_3145_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_postponed_3146_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_diag_3147_);
v___x_3164_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_st_ref_put(v_a_3059_, v___x_3164_);
if (v_isShared_3141_ == 0)
{
v___x_3167_ = v___x_3140_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3137_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3137_);
lean_dec(v_a_3131_);
return v___x_3136_;
}
}
else
{
lean_dec(v_a_3131_);
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_us_3110_);
lean_dec(v_declName_3109_);
v_a_3197_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3130_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3130_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
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
lean_dec_ref_known(v_e_3057_, 2);
goto v___jp_3111_;
}
}
}
v___jp_3111_:
{
lean_object* v_toCold_3112_; lean_object* v_cancelTk_x3f_3113_; 
v_toCold_3112_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3113_ = lean_ctor_get(v_toCold_3112_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3113_) == 1)
{
lean_object* v_val_3114_; uint8_t v___x_3115_; 
v_val_3114_ = lean_ctor_get(v_cancelTk_x3f_3113_, 0);
v___x_3115_ = l_IO_CancelToken_isSet(v_val_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3109_, v_us_3110_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_us_3110_);
lean_dec(v_declName_3109_);
v___x_3117_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3109_, v_us_3110_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3126_;
}
}
}
case 5:
{
lean_object* v_fn_3205_; uint8_t v_cacheInferType_3206_; lean_object* v_nargs_3207_; lean_object* v___x_3208_; lean_object* v_dummy_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_fn_3205_ = lean_ctor_get(v_e_3057_, 0);
v_cacheInferType_3206_ = lean_ctor_get_uint8(v_a_3058_, sizeof(void*)*7 + 3);
v_nargs_3207_ = l_Lean_Expr_getAppNumArgs(v_e_3057_);
v___x_3208_ = l_Lean_Expr_getAppFn(v_fn_3205_);
v_dummy_3209_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3207_);
v___x_3210_ = lean_mk_array(v_nargs_3207_, v_dummy_3209_);
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = lean_nat_sub(v_nargs_3207_, v___x_3211_);
lean_dec(v_nargs_3207_);
lean_inc_ref(v_e_3057_);
v___x_3213_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3057_, v___x_3210_, v___x_3212_);
if (v_cacheInferType_3206_ == 0)
{
lean_dec_ref_known(v_e_3057_, 2);
goto v___jp_3214_;
}
else
{
uint8_t v___x_3230_; 
v___x_3230_ = l_Lean_Expr_hasMVar(v_e_3057_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3297_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3297_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3297_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3276_; lean_object* v_cache_3277_; lean_object* v_inferType_3278_; lean_object* v___x_3279_; 
v___x_3276_ = lean_st_ref_get(v_a_3059_);
v_cache_3277_ = lean_ctor_get(v___x_3276_, 1);
lean_inc_ref(v_cache_3277_);
lean_dec(v___x_3276_);
v_inferType_3278_ = lean_ctor_get(v_cache_3277_, 0);
lean_inc_ref(v_inferType_3278_);
lean_dec_ref(v_cache_3277_);
v___x_3279_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3278_, v_a_3232_);
lean_dec_ref(v_inferType_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_toCold_3280_; lean_object* v_cancelTk_x3f_3281_; 
lean_del_object(v___x_3234_);
v_toCold_3280_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3281_ = lean_ctor_get(v_toCold_3280_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3281_) == 1)
{
lean_object* v_val_3282_; uint8_t v___x_3283_; 
v_val_3282_ = lean_ctor_get(v_cancelTk_x3f_3281_, 0);
v___x_3283_ = l_IO_CancelToken_isSet(v_val_3282_);
if (v___x_3283_ == 0)
{
goto v___jp_3236_;
}
else
{
lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_a_3232_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v___x_3208_);
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
goto v___jp_3236_;
}
}
else
{
lean_object* v_val_3293_; lean_object* v___x_3295_; 
lean_dec(v_a_3232_);
lean_dec_ref(v___x_3213_);
lean_dec_ref(v___x_3208_);
v_val_3293_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___x_3279_, 1);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_val_3293_);
v___x_3295_ = v___x_3234_;
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
v___jp_3236_:
{
lean_object* v___x_3237_; 
v___x_3237_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3208_, v___x_3213_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec_ref(v___x_3213_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; uint8_t v___x_3239_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
v___x_3239_ = l_Lean_Expr_hasMVar(v_a_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3274_; 
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v___x_3237_, 0);
lean_dec(v_unused_3275_);
v___x_3241_ = v___x_3237_;
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v___x_3237_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v_cache_3244_; lean_object* v_mctx_3245_; lean_object* v_zetaDeltaFVarIds_3246_; lean_object* v_postponed_3247_; lean_object* v_diag_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3273_; 
v___x_3243_ = lean_st_ref_take(v_a_3059_);
v_cache_3244_ = lean_ctor_get(v___x_3243_, 1);
v_mctx_3245_ = lean_ctor_get(v___x_3243_, 0);
v_zetaDeltaFVarIds_3246_ = lean_ctor_get(v___x_3243_, 2);
v_postponed_3247_ = lean_ctor_get(v___x_3243_, 3);
v_diag_3248_ = lean_ctor_get(v___x_3243_, 4);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3250_ = v___x_3243_;
v_isShared_3251_ = v_isSharedCheck_3273_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_diag_3248_);
lean_inc(v_postponed_3247_);
lean_inc(v_zetaDeltaFVarIds_3246_);
lean_inc(v_cache_3244_);
lean_inc(v_mctx_3245_);
lean_dec(v___x_3243_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3273_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v_inferType_3252_; lean_object* v_funInfo_3253_; lean_object* v_synthInstance_3254_; lean_object* v_whnf_3255_; lean_object* v_defEqTrans_3256_; lean_object* v_defEqPerm_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3272_; 
v_inferType_3252_ = lean_ctor_get(v_cache_3244_, 0);
v_funInfo_3253_ = lean_ctor_get(v_cache_3244_, 1);
v_synthInstance_3254_ = lean_ctor_get(v_cache_3244_, 2);
v_whnf_3255_ = lean_ctor_get(v_cache_3244_, 3);
v_defEqTrans_3256_ = lean_ctor_get(v_cache_3244_, 4);
v_defEqPerm_3257_ = lean_ctor_get(v_cache_3244_, 5);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_cache_3244_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3259_ = v_cache_3244_;
v_isShared_3260_ = v_isSharedCheck_3272_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_defEqPerm_3257_);
lean_inc(v_defEqTrans_3256_);
lean_inc(v_whnf_3255_);
lean_inc(v_synthInstance_3254_);
lean_inc(v_funInfo_3253_);
lean_inc(v_inferType_3252_);
lean_dec(v_cache_3244_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3272_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
lean_inc(v_a_3238_);
v___x_3261_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3252_, v_a_3232_, v_a_3238_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3261_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_funInfo_3253_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_synthInstance_3254_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_whnf_3255_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_defEqTrans_3256_);
lean_ctor_set(v_reuseFailAlloc_3271_, 5, v_defEqPerm_3257_);
v___x_3263_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3265_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v___x_3263_);
v___x_3265_ = v___x_3250_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_mctx_3245_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3270_, 2, v_zetaDeltaFVarIds_3246_);
lean_ctor_set(v_reuseFailAlloc_3270_, 3, v_postponed_3247_);
lean_ctor_set(v_reuseFailAlloc_3270_, 4, v_diag_3248_);
v___x_3265_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_st_ref_put(v_a_3059_, v___x_3265_);
if (v_isShared_3242_ == 0)
{
v___x_3268_ = v___x_3241_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3238_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3238_);
lean_dec(v_a_3232_);
return v___x_3237_;
}
}
else
{
lean_dec(v_a_3232_);
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v___x_3213_);
lean_dec_ref(v___x_3208_);
v_a_3298_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3231_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3231_);
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
lean_dec_ref_known(v_e_3057_, 2);
goto v___jp_3214_;
}
}
v___jp_3214_:
{
lean_object* v_toCold_3215_; lean_object* v_cancelTk_x3f_3216_; 
v_toCold_3215_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3216_ = lean_ctor_get(v_toCold_3215_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3216_) == 1)
{
lean_object* v_val_3217_; uint8_t v___x_3218_; 
v_val_3217_ = lean_ctor_get(v_cancelTk_x3f_3216_, 0);
v___x_3218_ = l_IO_CancelToken_isSet(v_val_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3208_, v___x_3213_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec_ref(v___x_3213_);
return v___x_3219_;
}
else
{
lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec_ref(v___x_3213_);
lean_dec_ref(v___x_3208_);
v___x_3220_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3208_, v___x_3213_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec_ref(v___x_3213_);
return v___x_3229_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3306_; 
v_cacheInferType_3306_ = lean_ctor_get_uint8(v_a_3058_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3306_ == 0)
{
goto v___jp_3079_;
}
else
{
uint8_t v___x_3307_; 
v___x_3307_ = l_Lean_Expr_hasMVar(v_e_3057_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_inc_ref(v_e_3057_);
v___x_3308_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3374_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3374_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3374_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3353_; lean_object* v_cache_3354_; lean_object* v_inferType_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_st_ref_get(v_a_3059_);
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
lean_object* v_toCold_3357_; lean_object* v_cancelTk_x3f_3358_; 
lean_del_object(v___x_3311_);
v_toCold_3357_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3358_ = lean_ctor_get(v_toCold_3357_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3358_) == 1)
{
lean_object* v_val_3359_; uint8_t v___x_3360_; 
v_val_3359_ = lean_ctor_get(v_cancelTk_x3f_3358_, 0);
v___x_3360_ = l_IO_CancelToken_isSet(v_val_3359_);
if (v___x_3360_ == 0)
{
goto v___jp_3313_;
}
else
{
lean_object* v___x_3361_; lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3309_);
lean_dec_ref_known(v_e_3057_, 3);
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
goto v___jp_3313_;
}
}
else
{
lean_object* v_val_3370_; lean_object* v___x_3372_; 
lean_dec(v_a_3309_);
lean_dec_ref_known(v_e_3057_, 3);
v_val_3370_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v___x_3356_, 1);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_val_3370_);
v___x_3372_ = v___x_3311_;
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
v___jp_3313_:
{
lean_object* v___x_3314_; 
v___x_3314_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
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
v___x_3320_ = lean_st_ref_take(v_a_3059_);
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
v___x_3343_ = lean_st_ref_put(v_a_3059_, v___x_3342_);
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
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref_known(v_e_3057_, 3);
v_a_3375_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3308_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3308_);
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
goto v___jp_3079_;
}
}
}
case 9:
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_a_3383_ = lean_ctor_get(v_e_3057_, 0);
lean_inc_ref(v_a_3383_);
lean_dec_ref_known(v_e_3057_, 1);
v___x_3384_ = l_Lean_Literal_type(v_a_3383_);
lean_dec_ref(v_a_3383_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
case 10:
{
lean_object* v_expr_3386_; 
v_expr_3386_ = lean_ctor_get(v_e_3057_, 1);
lean_inc_ref(v_expr_3386_);
lean_dec_ref_known(v_e_3057_, 2);
v_e_3057_ = v_expr_3386_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3388_; lean_object* v_idx_3389_; lean_object* v_struct_3390_; uint8_t v_cacheInferType_3407_; 
v_typeName_3388_ = lean_ctor_get(v_e_3057_, 0);
lean_inc(v_typeName_3388_);
v_idx_3389_ = lean_ctor_get(v_e_3057_, 1);
lean_inc(v_idx_3389_);
v_struct_3390_ = lean_ctor_get(v_e_3057_, 2);
lean_inc_ref(v_struct_3390_);
v_cacheInferType_3407_ = lean_ctor_get_uint8(v_a_3058_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3407_ == 0)
{
lean_dec_ref_known(v_e_3057_, 3);
goto v___jp_3391_;
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = l_Lean_Expr_hasMVar(v_e_3057_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3475_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3475_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3475_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3454_; lean_object* v_cache_3455_; lean_object* v_inferType_3456_; lean_object* v___x_3457_; 
v___x_3454_ = lean_st_ref_get(v_a_3059_);
v_cache_3455_ = lean_ctor_get(v___x_3454_, 1);
lean_inc_ref(v_cache_3455_);
lean_dec(v___x_3454_);
v_inferType_3456_ = lean_ctor_get(v_cache_3455_, 0);
lean_inc_ref(v_inferType_3456_);
lean_dec_ref(v_cache_3455_);
v___x_3457_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3456_, v_a_3410_);
lean_dec_ref(v_inferType_3456_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_toCold_3458_; lean_object* v_cancelTk_x3f_3459_; 
lean_del_object(v___x_3412_);
v_toCold_3458_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3459_ = lean_ctor_get(v_toCold_3458_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3459_) == 1)
{
lean_object* v_val_3460_; uint8_t v___x_3461_; 
v_val_3460_ = lean_ctor_get(v_cancelTk_x3f_3459_, 0);
v___x_3461_ = l_IO_CancelToken_isSet(v_val_3460_);
if (v___x_3461_ == 0)
{
goto v___jp_3414_;
}
else
{
lean_object* v___x_3462_; lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3410_);
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v___x_3462_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
goto v___jp_3414_;
}
}
else
{
lean_object* v_val_3471_; lean_object* v___x_3473_; 
lean_dec(v_a_3410_);
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v_val_3471_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v___x_3457_, 1);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v_val_3471_);
v___x_3473_ = v___x_3412_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_val_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
v___jp_3414_:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; uint8_t v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
v___x_3417_ = l_Lean_Expr_hasMVar(v_a_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3452_; 
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___x_3415_, 0);
lean_dec(v_unused_3453_);
v___x_3419_ = v___x_3415_;
v_isShared_3420_ = v_isSharedCheck_3452_;
goto v_resetjp_3418_;
}
else
{
lean_dec(v___x_3415_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3452_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v_cache_3422_; lean_object* v_mctx_3423_; lean_object* v_zetaDeltaFVarIds_3424_; lean_object* v_postponed_3425_; lean_object* v_diag_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3451_; 
v___x_3421_ = lean_st_ref_take(v_a_3059_);
v_cache_3422_ = lean_ctor_get(v___x_3421_, 1);
v_mctx_3423_ = lean_ctor_get(v___x_3421_, 0);
v_zetaDeltaFVarIds_3424_ = lean_ctor_get(v___x_3421_, 2);
v_postponed_3425_ = lean_ctor_get(v___x_3421_, 3);
v_diag_3426_ = lean_ctor_get(v___x_3421_, 4);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3428_ = v___x_3421_;
v_isShared_3429_ = v_isSharedCheck_3451_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_diag_3426_);
lean_inc(v_postponed_3425_);
lean_inc(v_zetaDeltaFVarIds_3424_);
lean_inc(v_cache_3422_);
lean_inc(v_mctx_3423_);
lean_dec(v___x_3421_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3451_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_inferType_3430_; lean_object* v_funInfo_3431_; lean_object* v_synthInstance_3432_; lean_object* v_whnf_3433_; lean_object* v_defEqTrans_3434_; lean_object* v_defEqPerm_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3450_; 
v_inferType_3430_ = lean_ctor_get(v_cache_3422_, 0);
v_funInfo_3431_ = lean_ctor_get(v_cache_3422_, 1);
v_synthInstance_3432_ = lean_ctor_get(v_cache_3422_, 2);
v_whnf_3433_ = lean_ctor_get(v_cache_3422_, 3);
v_defEqTrans_3434_ = lean_ctor_get(v_cache_3422_, 4);
v_defEqPerm_3435_ = lean_ctor_get(v_cache_3422_, 5);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_cache_3422_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3437_ = v_cache_3422_;
v_isShared_3438_ = v_isSharedCheck_3450_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_defEqPerm_3435_);
lean_inc(v_defEqTrans_3434_);
lean_inc(v_whnf_3433_);
lean_inc(v_synthInstance_3432_);
lean_inc(v_funInfo_3431_);
lean_inc(v_inferType_3430_);
lean_dec(v_cache_3422_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3450_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
lean_inc(v_a_3416_);
v___x_3439_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3430_, v_a_3410_, v_a_3416_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_funInfo_3431_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_synthInstance_3432_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_whnf_3433_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_defEqTrans_3434_);
lean_ctor_set(v_reuseFailAlloc_3449_, 5, v_defEqPerm_3435_);
v___x_3441_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3443_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v___x_3441_);
v___x_3443_ = v___x_3428_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_mctx_3423_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_zetaDeltaFVarIds_3424_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_postponed_3425_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_diag_3426_);
v___x_3443_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3444_ = lean_st_ref_put(v_a_3059_, v___x_3443_);
if (v_isShared_3420_ == 0)
{
v___x_3446_ = v___x_3419_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3416_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3416_);
lean_dec(v_a_3410_);
return v___x_3415_;
}
}
else
{
lean_dec(v_a_3410_);
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v_a_3476_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3409_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3409_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3057_, 3);
goto v___jp_3391_;
}
}
v___jp_3391_:
{
lean_object* v_toCold_3392_; lean_object* v_cancelTk_x3f_3393_; 
v_toCold_3392_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3393_ = lean_ctor_get(v_toCold_3392_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3393_) == 1)
{
lean_object* v_val_3394_; uint8_t v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_cancelTk_x3f_3393_, 0);
v___x_3395_ = l_IO_CancelToken_isSet(v_val_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3396_;
}
else
{
lean_object* v___x_3397_; lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v_struct_3390_);
lean_dec(v_idx_3389_);
lean_dec(v_typeName_3388_);
v___x_3397_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3388_, v_idx_3389_, v_struct_3390_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3406_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3484_; 
v_cacheInferType_3484_ = lean_ctor_get_uint8(v_a_3058_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3484_ == 0)
{
goto v___jp_3063_;
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = l_Lean_Expr_hasMVar(v_e_3057_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_inc_ref(v_e_3057_);
v___x_3486_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3552_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3552_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3552_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3531_; lean_object* v_cache_3532_; lean_object* v_inferType_3533_; lean_object* v___x_3534_; 
v___x_3531_ = lean_st_ref_get(v_a_3059_);
v_cache_3532_ = lean_ctor_get(v___x_3531_, 1);
lean_inc_ref(v_cache_3532_);
lean_dec(v___x_3531_);
v_inferType_3533_ = lean_ctor_get(v_cache_3532_, 0);
lean_inc_ref(v_inferType_3533_);
lean_dec_ref(v_cache_3532_);
v___x_3534_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3533_, v_a_3487_);
lean_dec_ref(v_inferType_3533_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_toCold_3535_; lean_object* v_cancelTk_x3f_3536_; 
lean_del_object(v___x_3489_);
v_toCold_3535_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3536_ = lean_ctor_get(v_toCold_3535_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3536_) == 1)
{
lean_object* v_val_3537_; uint8_t v___x_3538_; 
v_val_3537_ = lean_ctor_get(v_cancelTk_x3f_3536_, 0);
v___x_3538_ = l_IO_CancelToken_isSet(v_val_3537_);
if (v___x_3538_ == 0)
{
goto v___jp_3491_;
}
else
{
lean_object* v___x_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_e_3057_);
v___x_3539_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
goto v___jp_3491_;
}
}
else
{
lean_object* v_val_3548_; lean_object* v___x_3550_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_e_3057_);
v_val_3548_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v___x_3534_, 1);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v_val_3548_);
v___x_3550_ = v___x_3489_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_val_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
v___jp_3491_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; uint8_t v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
v___x_3494_ = l_Lean_Expr_hasMVar(v_a_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3529_; 
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v___x_3492_, 0);
lean_dec(v_unused_3530_);
v___x_3496_ = v___x_3492_;
v_isShared_3497_ = v_isSharedCheck_3529_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3529_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v_cache_3499_; lean_object* v_mctx_3500_; lean_object* v_zetaDeltaFVarIds_3501_; lean_object* v_postponed_3502_; lean_object* v_diag_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3528_; 
v___x_3498_ = lean_st_ref_take(v_a_3059_);
v_cache_3499_ = lean_ctor_get(v___x_3498_, 1);
v_mctx_3500_ = lean_ctor_get(v___x_3498_, 0);
v_zetaDeltaFVarIds_3501_ = lean_ctor_get(v___x_3498_, 2);
v_postponed_3502_ = lean_ctor_get(v___x_3498_, 3);
v_diag_3503_ = lean_ctor_get(v___x_3498_, 4);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3505_ = v___x_3498_;
v_isShared_3506_ = v_isSharedCheck_3528_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_diag_3503_);
lean_inc(v_postponed_3502_);
lean_inc(v_zetaDeltaFVarIds_3501_);
lean_inc(v_cache_3499_);
lean_inc(v_mctx_3500_);
lean_dec(v___x_3498_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3528_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_inferType_3507_; lean_object* v_funInfo_3508_; lean_object* v_synthInstance_3509_; lean_object* v_whnf_3510_; lean_object* v_defEqTrans_3511_; lean_object* v_defEqPerm_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3527_; 
v_inferType_3507_ = lean_ctor_get(v_cache_3499_, 0);
v_funInfo_3508_ = lean_ctor_get(v_cache_3499_, 1);
v_synthInstance_3509_ = lean_ctor_get(v_cache_3499_, 2);
v_whnf_3510_ = lean_ctor_get(v_cache_3499_, 3);
v_defEqTrans_3511_ = lean_ctor_get(v_cache_3499_, 4);
v_defEqPerm_3512_ = lean_ctor_get(v_cache_3499_, 5);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_cache_3499_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3514_ = v_cache_3499_;
v_isShared_3515_ = v_isSharedCheck_3527_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_defEqPerm_3512_);
lean_inc(v_defEqTrans_3511_);
lean_inc(v_whnf_3510_);
lean_inc(v_synthInstance_3509_);
lean_inc(v_funInfo_3508_);
lean_inc(v_inferType_3507_);
lean_dec(v_cache_3499_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3527_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_inc(v_a_3493_);
v___x_3516_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3507_, v_a_3487_, v_a_3493_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3516_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_funInfo_3508_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_synthInstance_3509_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_whnf_3510_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_defEqTrans_3511_);
lean_ctor_set(v_reuseFailAlloc_3526_, 5, v_defEqPerm_3512_);
v___x_3518_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3518_);
v___x_3520_ = v___x_3505_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_mctx_3500_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_zetaDeltaFVarIds_3501_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_postponed_3502_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_diag_3503_);
v___x_3520_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_st_ref_put(v_a_3059_, v___x_3520_);
if (v_isShared_3497_ == 0)
{
v___x_3523_ = v___x_3496_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3493_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3493_);
lean_dec(v_a_3487_);
return v___x_3492_;
}
}
else
{
lean_dec(v_a_3487_);
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v_e_3057_);
v_a_3553_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3486_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3486_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
goto v___jp_3063_;
}
}
}
}
v___jp_3063_:
{
lean_object* v_toCold_3064_; lean_object* v_cancelTk_x3f_3065_; 
v_toCold_3064_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3065_ = lean_ctor_get(v_toCold_3064_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3065_) == 1)
{
lean_object* v_val_3066_; uint8_t v___x_3067_; 
v_val_3066_ = lean_ctor_get(v_cancelTk_x3f_3065_, 0);
v___x_3067_ = l_IO_CancelToken_isSet(v_val_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v_e_3057_);
v___x_3069_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3078_;
}
}
v___jp_3079_:
{
lean_object* v_toCold_3080_; lean_object* v_cancelTk_x3f_3081_; 
v_toCold_3080_ = lean_ctor_get(v_a_3060_, 0);
v_cancelTk_x3f_3081_ = lean_ctor_get(v_toCold_3080_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3081_) == 1)
{
lean_object* v_val_3082_; uint8_t v___x_3083_; 
v_val_3082_ = lean_ctor_get(v_cancelTk_x3f_3081_, 0);
v___x_3083_ = l_IO_CancelToken_isSet(v_val_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_e_3057_);
v___x_3085_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3569_, v_x_3570_, v_x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3574_, v_x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3577_, lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3577_, v_x_3578_, v_x_3579_);
lean_dec_ref(v_x_3579_);
lean_dec_ref(v_x_3578_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3581_, lean_object* v_x_3582_, size_t v_x_3583_, size_t v_x_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3582_, v_x_3583_, v_x_3584_, v_x_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
size_t v_x_4028__boxed_3594_; size_t v_x_4029__boxed_3595_; lean_object* v_res_3596_; 
v_x_4028__boxed_3594_ = lean_unbox_usize(v_x_3590_);
lean_dec(v_x_3590_);
v_x_4029__boxed_3595_ = lean_unbox_usize(v_x_3591_);
lean_dec(v_x_3591_);
v_res_3596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3588_, v_x_3589_, v_x_4028__boxed_3594_, v_x_4029__boxed_3595_, v_x_3592_, v_x_3593_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3597_, lean_object* v_x_3598_, size_t v_x_3599_, lean_object* v_x_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3598_, v_x_3599_, v_x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
size_t v_x_4045__boxed_3606_; lean_object* v_res_3607_; 
v_x_4045__boxed_3606_ = lean_unbox_usize(v_x_3604_);
lean_dec(v_x_3604_);
v_res_3607_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3602_, v_x_3603_, v_x_4045__boxed_3606_, v_x_3605_);
lean_dec_ref(v_x_3605_);
lean_dec_ref(v_x_3603_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3608_, lean_object* v_n_3609_, lean_object* v_k_3610_, lean_object* v_v_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3609_, v_k_3610_, v_v_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3613_, size_t v_depth_3614_, lean_object* v_keys_3615_, lean_object* v_vals_3616_, lean_object* v_heq_3617_, lean_object* v_i_3618_, lean_object* v_entries_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3614_, v_keys_3615_, v_vals_3616_, v_i_3618_, v_entries_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3621_, lean_object* v_depth_3622_, lean_object* v_keys_3623_, lean_object* v_vals_3624_, lean_object* v_heq_3625_, lean_object* v_i_3626_, lean_object* v_entries_3627_){
_start:
{
size_t v_depth_boxed_3628_; lean_object* v_res_3629_; 
v_depth_boxed_3628_ = lean_unbox_usize(v_depth_3622_);
lean_dec(v_depth_3622_);
v_res_3629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3621_, v_depth_boxed_3628_, v_keys_3623_, v_vals_3624_, v_heq_3625_, v_i_3626_, v_entries_3627_);
lean_dec_ref(v_vals_3624_);
lean_dec_ref(v_keys_3623_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3630_, lean_object* v_keys_3631_, lean_object* v_vals_3632_, lean_object* v_heq_3633_, lean_object* v_i_3634_, lean_object* v_k_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3631_, v_vals_3632_, v_i_3634_, v_k_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3637_, lean_object* v_keys_3638_, lean_object* v_vals_3639_, lean_object* v_heq_3640_, lean_object* v_i_3641_, lean_object* v_k_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3637_, v_keys_3638_, v_vals_3639_, v_heq_3640_, v_i_3641_, v_k_3642_);
lean_dec_ref(v_k_3642_);
lean_dec_ref(v_vals_3639_);
lean_dec_ref(v_keys_3638_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3645_, v_x_3646_, v_x_3647_, v_x_3648_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = l_Lean_maxRecDepthErrorMessage;
v___x_3656_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3658_ = l_Lean_MessageData_ofFormat(v___x_3657_);
return v___x_3658_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3660_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3661_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3662_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_ref_3662_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3670_, lean_object* v_ref_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3671_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3678_, lean_object* v_ref_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3678_, v_ref_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3738_; uint8_t v_beta_3739_; 
v___x_3738_ = l_Lean_Meta_Context_config(v___y_3687_);
v_beta_3739_ = lean_ctor_get_uint8(v___x_3738_, 13);
if (v_beta_3739_ == 0)
{
lean_dec_ref(v___x_3738_);
goto v___jp_3692_;
}
else
{
uint8_t v_iota_3740_; 
v_iota_3740_ = lean_ctor_get_uint8(v___x_3738_, 12);
if (v_iota_3740_ == 0)
{
lean_dec_ref(v___x_3738_);
goto v___jp_3692_;
}
else
{
uint8_t v_zeta_3741_; 
v_zeta_3741_ = lean_ctor_get_uint8(v___x_3738_, 15);
if (v_zeta_3741_ == 0)
{
lean_dec_ref(v___x_3738_);
goto v___jp_3692_;
}
else
{
uint8_t v_zetaHave_3742_; 
v_zetaHave_3742_ = lean_ctor_get_uint8(v___x_3738_, 18);
if (v_zetaHave_3742_ == 0)
{
lean_dec_ref(v___x_3738_);
goto v___jp_3692_;
}
else
{
uint8_t v_zetaDelta_3743_; 
v_zetaDelta_3743_ = lean_ctor_get_uint8(v___x_3738_, 16);
if (v_zetaDelta_3743_ == 0)
{
lean_dec_ref(v___x_3738_);
goto v___jp_3692_;
}
else
{
uint8_t v_etaStruct_3744_; uint8_t v_proj_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_etaStruct_3744_ = lean_ctor_get_uint8(v___x_3738_, 10);
v_proj_3745_ = lean_ctor_get_uint8(v___x_3738_, 14);
lean_dec_ref(v___x_3738_);
v___x_3746_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_3745_);
v___x_3747_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_3748_ = lean_nat_dec_eq(v___x_3746_, v___x_3747_);
lean_dec(v___x_3746_);
if (v___x_3748_ == 0)
{
goto v___jp_3692_;
}
else
{
uint8_t v___x_3749_; uint8_t v___x_3750_; 
v___x_3749_ = 0;
v___x_3750_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3744_, v___x_3749_);
if (v___x_3750_ == 0)
{
goto v___jp_3692_;
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec_ref(v___y_3687_);
return v___x_3751_;
}
}
}
}
}
}
}
v___jp_3692_:
{
lean_object* v___x_3693_; uint8_t v_foApprox_3694_; uint8_t v_ctxApprox_3695_; uint8_t v_quasiPatternApprox_3696_; uint8_t v_constApprox_3697_; uint8_t v_isDefEqStuckEx_3698_; uint8_t v_unificationHints_3699_; uint8_t v_proofIrrelevance_3700_; uint8_t v_assignSyntheticOpaque_3701_; uint8_t v_offsetCnstrs_3702_; uint8_t v_transparency_3703_; uint8_t v_univApprox_3704_; uint8_t v_zetaUnused_3705_; uint8_t v_canUnfoldPredicateConfig_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3737_; 
v___x_3693_ = l_Lean_Meta_Context_config(v___y_3687_);
v_foApprox_3694_ = lean_ctor_get_uint8(v___x_3693_, 0);
v_ctxApprox_3695_ = lean_ctor_get_uint8(v___x_3693_, 1);
v_quasiPatternApprox_3696_ = lean_ctor_get_uint8(v___x_3693_, 2);
v_constApprox_3697_ = lean_ctor_get_uint8(v___x_3693_, 3);
v_isDefEqStuckEx_3698_ = lean_ctor_get_uint8(v___x_3693_, 4);
v_unificationHints_3699_ = lean_ctor_get_uint8(v___x_3693_, 5);
v_proofIrrelevance_3700_ = lean_ctor_get_uint8(v___x_3693_, 6);
v_assignSyntheticOpaque_3701_ = lean_ctor_get_uint8(v___x_3693_, 7);
v_offsetCnstrs_3702_ = lean_ctor_get_uint8(v___x_3693_, 8);
v_transparency_3703_ = lean_ctor_get_uint8(v___x_3693_, 9);
v_univApprox_3704_ = lean_ctor_get_uint8(v___x_3693_, 11);
v_zetaUnused_3705_ = lean_ctor_get_uint8(v___x_3693_, 17);
v_canUnfoldPredicateConfig_3706_ = lean_ctor_get_uint8(v___x_3693_, 19);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3708_ = v___x_3693_;
v_isShared_3709_ = v_isSharedCheck_3737_;
goto v_resetjp_3707_;
}
else
{
lean_dec(v___x_3693_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3737_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
uint8_t v___x_3710_; uint8_t v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3714_; 
v___x_3710_ = 1;
v___x_3711_ = 0;
v___x_3712_ = 2;
if (v_isShared_3709_ == 0)
{
v___x_3714_ = v___x_3708_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 0, v_foApprox_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 1, v_ctxApprox_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 2, v_quasiPatternApprox_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 3, v_constApprox_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 4, v_isDefEqStuckEx_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 5, v_unificationHints_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 6, v_proofIrrelevance_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 7, v_assignSyntheticOpaque_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 8, v_offsetCnstrs_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 9, v_transparency_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 11, v_univApprox_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 17, v_zetaUnused_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, 19, v_canUnfoldPredicateConfig_3706_);
v___x_3714_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
uint8_t v_trackZetaDelta_3715_; lean_object* v_zetaDeltaSet_3716_; lean_object* v_lctx_3717_; lean_object* v_localInstances_3718_; lean_object* v_defEqCtx_x3f_3719_; lean_object* v_synthPendingDepth_3720_; lean_object* v_customCanUnfoldPredicate_x3f_3721_; uint8_t v_univApprox_3722_; uint8_t v_inTypeClassResolution_3723_; uint8_t v_cacheInferType_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3734_; 
lean_ctor_set_uint8(v___x_3714_, 10, v___x_3711_);
lean_ctor_set_uint8(v___x_3714_, 12, v___x_3710_);
lean_ctor_set_uint8(v___x_3714_, 13, v___x_3710_);
lean_ctor_set_uint8(v___x_3714_, 14, v___x_3712_);
lean_ctor_set_uint8(v___x_3714_, 15, v___x_3710_);
lean_ctor_set_uint8(v___x_3714_, 16, v___x_3710_);
lean_ctor_set_uint8(v___x_3714_, 18, v___x_3710_);
v_trackZetaDelta_3715_ = lean_ctor_get_uint8(v___y_3687_, sizeof(void*)*7);
v_zetaDeltaSet_3716_ = lean_ctor_get(v___y_3687_, 1);
v_lctx_3717_ = lean_ctor_get(v___y_3687_, 2);
v_localInstances_3718_ = lean_ctor_get(v___y_3687_, 3);
v_defEqCtx_x3f_3719_ = lean_ctor_get(v___y_3687_, 4);
v_synthPendingDepth_3720_ = lean_ctor_get(v___y_3687_, 5);
v_customCanUnfoldPredicate_x3f_3721_ = lean_ctor_get(v___y_3687_, 6);
v_univApprox_3722_ = lean_ctor_get_uint8(v___y_3687_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3723_ = lean_ctor_get_uint8(v___y_3687_, sizeof(void*)*7 + 2);
v_cacheInferType_3724_ = lean_ctor_get_uint8(v___y_3687_, sizeof(void*)*7 + 3);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___y_3687_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v___y_3687_, 0);
lean_dec(v_unused_3735_);
v___x_3726_ = v___y_3687_;
v_isShared_3727_ = v_isSharedCheck_3734_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3721_);
lean_inc(v_synthPendingDepth_3720_);
lean_inc(v_defEqCtx_x3f_3719_);
lean_inc(v_localInstances_3718_);
lean_inc(v_lctx_3717_);
lean_inc(v_zetaDeltaSet_3716_);
lean_dec(v___y_3687_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3734_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
uint64_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3728_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3714_);
v___x_3729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3729_, 0, v___x_3714_);
lean_ctor_set_uint64(v___x_3729_, sizeof(void*)*1, v___x_3728_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3729_);
v___x_3731_ = v___x_3726_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_zetaDeltaSet_3716_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_lctx_3717_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_localInstances_3718_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_defEqCtx_x3f_3719_);
lean_ctor_set(v_reuseFailAlloc_3733_, 5, v_synthPendingDepth_3720_);
lean_ctor_set(v_reuseFailAlloc_3733_, 6, v_customCanUnfoldPredicate_x3f_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*7, v_trackZetaDelta_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*7 + 1, v_univApprox_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*7 + 3, v_cacheInferType_3724_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3686_, v___x_3731_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec_ref(v___x_3731_);
return v___x_3732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v___y_3766_; lean_object* v_toCold_3783_; lean_object* v_currRecDepth_3784_; lean_object* v_ref_3785_; uint8_t v_diag_3786_; uint8_t v_suppressElabErrors_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3827_; 
v_toCold_3783_ = lean_ctor_get(v_a_3762_, 0);
v_currRecDepth_3784_ = lean_ctor_get(v_a_3762_, 1);
v_ref_3785_ = lean_ctor_get(v_a_3762_, 2);
v_diag_3786_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*3);
v_suppressElabErrors_3787_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*3 + 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3789_ = v_a_3762_;
v_isShared_3790_ = v_isSharedCheck_3827_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_ref_3785_);
lean_inc(v_currRecDepth_3784_);
lean_inc(v_toCold_3783_);
lean_dec(v_a_3762_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3827_;
goto v_resetjp_3788_;
}
v___jp_3765_:
{
if (lean_obj_tag(v___y_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
v_a_3767_ = lean_ctor_get(v___y_3766_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___y_3766_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___y_3766_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___y_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_a_3775_ = lean_ctor_get(v___y_3766_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___y_3766_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___y_3766_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___y_3766_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
v_resetjp_3788_:
{
lean_object* v_maxRecDepth_3791_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_maxRecDepth_3791_ = lean_ctor_get(v_toCold_3783_, 3);
v___x_3823_ = lean_unsigned_to_nat(0u);
v___x_3824_ = lean_nat_dec_eq(v_maxRecDepth_3791_, v___x_3823_);
if (v___x_3824_ == 0)
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_nat_dec_eq(v_currRecDepth_3784_, v_maxRecDepth_3791_);
if (v___x_3825_ == 0)
{
goto v___jp_3792_;
}
else
{
lean_object* v___x_3826_; 
lean_del_object(v___x_3789_);
lean_dec(v_currRecDepth_3784_);
lean_dec_ref(v_toCold_3783_);
lean_dec(v_a_3763_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec_ref(v_e_3759_);
v___x_3826_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3785_);
return v___x_3826_;
}
}
else
{
goto v___jp_3792_;
}
v___jp_3792_:
{
lean_object* v___x_3793_; uint8_t v_transparency_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3793_ = l_Lean_Meta_Context_config(v_a_3760_);
v_transparency_3794_ = lean_ctor_get_uint8(v___x_3793_, 9);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(1u);
v___x_3796_ = lean_nat_add(v_currRecDepth_3784_, v___x_3795_);
lean_dec(v_currRecDepth_3784_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v___x_3796_);
v___x_3798_ = v___x_3789_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_toCold_3783_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_ref_3785_);
lean_ctor_set_uint8(v_reuseFailAlloc_3822_, sizeof(void*)*3, v_diag_3786_);
lean_ctor_set_uint8(v_reuseFailAlloc_3822_, sizeof(void*)*3 + 1, v_suppressElabErrors_3787_);
v___x_3798_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
uint8_t v___x_3799_; uint8_t v___x_3800_; 
v___x_3799_ = 1;
v___x_3800_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3794_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3759_, v_a_3760_, v_a_3761_, v___x_3798_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v___x_3798_);
lean_dec(v_a_3761_);
v___y_3766_ = v___x_3801_;
goto v___jp_3765_;
}
else
{
lean_object* v_keyedConfig_3802_; uint8_t v_trackZetaDelta_3803_; lean_object* v_zetaDeltaSet_3804_; lean_object* v_lctx_3805_; lean_object* v_localInstances_3806_; lean_object* v_defEqCtx_x3f_3807_; lean_object* v_synthPendingDepth_3808_; lean_object* v_customCanUnfoldPredicate_x3f_3809_; uint8_t v_univApprox_3810_; uint8_t v_inTypeClassResolution_3811_; uint8_t v_cacheInferType_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3821_; 
v_keyedConfig_3802_ = lean_ctor_get(v_a_3760_, 0);
v_trackZetaDelta_3803_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7);
v_zetaDeltaSet_3804_ = lean_ctor_get(v_a_3760_, 1);
v_lctx_3805_ = lean_ctor_get(v_a_3760_, 2);
v_localInstances_3806_ = lean_ctor_get(v_a_3760_, 3);
v_defEqCtx_x3f_3807_ = lean_ctor_get(v_a_3760_, 4);
v_synthPendingDepth_3808_ = lean_ctor_get(v_a_3760_, 5);
v_customCanUnfoldPredicate_x3f_3809_ = lean_ctor_get(v_a_3760_, 6);
v_univApprox_3810_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3811_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 2);
v_cacheInferType_3812_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 3);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3760_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3814_ = v_a_3760_;
v_isShared_3815_ = v_isSharedCheck_3821_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3809_);
lean_inc(v_synthPendingDepth_3808_);
lean_inc(v_defEqCtx_x3f_3807_);
lean_inc(v_localInstances_3806_);
lean_inc(v_lctx_3805_);
lean_inc(v_zetaDeltaSet_3804_);
lean_inc(v_keyedConfig_3802_);
lean_dec(v_a_3760_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3821_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3816_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3799_, v_keyedConfig_3802_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v___x_3816_);
v___x_3818_ = v___x_3814_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_zetaDeltaSet_3804_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_lctx_3805_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_localInstances_3806_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_defEqCtx_x3f_3807_);
lean_ctor_set(v_reuseFailAlloc_3820_, 5, v_synthPendingDepth_3808_);
lean_ctor_set(v_reuseFailAlloc_3820_, 6, v_customCanUnfoldPredicate_x3f_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*7, v_trackZetaDelta_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*7 + 1, v_univApprox_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3820_, sizeof(void*)*7 + 3, v_cacheInferType_3812_);
v___x_3818_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3759_, v___x_3818_, v_a_3761_, v___x_3798_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v___x_3798_);
lean_dec(v_a_3761_);
v___y_3766_ = v___x_3819_;
goto v___jp_3765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = lean_infer_type(v_e_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
return v_res_3834_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3835_){
_start:
{
switch(lean_obj_tag(v_x_3835_))
{
case 0:
{
uint8_t v___x_3836_; 
v___x_3836_ = 1;
return v___x_3836_;
}
case 2:
{
lean_object* v_a_3837_; lean_object* v_a_3838_; uint8_t v___x_3839_; 
v_a_3837_ = lean_ctor_get(v_x_3835_, 0);
v_a_3838_ = lean_ctor_get(v_x_3835_, 1);
v___x_3839_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3837_);
if (v___x_3839_ == 0)
{
return v___x_3839_;
}
else
{
v_x_3835_ = v_a_3838_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v_x_3835_, 1);
v_x_3835_ = v_a_3841_;
goto _start;
}
default: 
{
uint8_t v___x_3843_; 
v___x_3843_ = 0;
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3844_){
_start:
{
uint8_t v_res_3845_; lean_object* v_r_3846_; 
v_res_3845_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3844_);
lean_dec(v_x_3844_);
v_r_3846_ = lean_box(v_res_3845_);
return v_r_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; lean_object* v_mctx_3851_; lean_object* v___x_3852_; lean_object* v_fst_3853_; lean_object* v_snd_3854_; lean_object* v___x_3855_; lean_object* v_cache_3856_; lean_object* v_zetaDeltaFVarIds_3857_; lean_object* v_postponed_3858_; lean_object* v_diag_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3868_; 
v___x_3850_ = lean_st_ref_get(v___y_3848_);
v_mctx_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc_ref(v_mctx_3851_);
lean_dec(v___x_3850_);
v___x_3852_ = lean_instantiate_level_mvars(v_mctx_3851_, v_l_3847_);
v_fst_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_fst_3853_);
v_snd_3854_ = lean_ctor_get(v___x_3852_, 1);
lean_inc(v_snd_3854_);
lean_dec_ref(v___x_3852_);
v___x_3855_ = lean_st_ref_take(v___y_3848_);
v_cache_3856_ = lean_ctor_get(v___x_3855_, 1);
v_zetaDeltaFVarIds_3857_ = lean_ctor_get(v___x_3855_, 2);
v_postponed_3858_ = lean_ctor_get(v___x_3855_, 3);
v_diag_3859_ = lean_ctor_get(v___x_3855_, 4);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; 
v_unused_3869_ = lean_ctor_get(v___x_3855_, 0);
lean_dec(v_unused_3869_);
v___x_3861_ = v___x_3855_;
v_isShared_3862_ = v_isSharedCheck_3868_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_diag_3859_);
lean_inc(v_postponed_3858_);
lean_inc(v_zetaDeltaFVarIds_3857_);
lean_inc(v_cache_3856_);
lean_dec(v___x_3855_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3868_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v_fst_3853_);
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_fst_3853_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_cache_3856_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_zetaDeltaFVarIds_3857_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_postponed_3858_);
lean_ctor_set(v_reuseFailAlloc_3867_, 4, v_diag_3859_);
v___x_3864_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_st_ref_put(v___y_3848_, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3866_, 0, v_snd_3854_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3870_, v___y_3871_);
lean_dec(v___y_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3874_, v___y_3876_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
switch(lean_obj_tag(v_x_3888_))
{
case 3:
{
lean_object* v_u_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_u_3899_ = lean_ctor_get(v_x_3888_, 0);
lean_inc(v_u_3899_);
lean_dec_ref_known(v_x_3888_, 1);
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_nat_dec_eq(v_x_3889_, v___x_3900_);
lean_dec(v_x_3889_);
if (v___x_3901_ == 0)
{
lean_dec(v_u_3899_);
goto v___jp_3895_;
}
else
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3899_, v_a_3891_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3913_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
uint8_t v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3907_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3903_);
lean_dec(v_a_3903_);
v___x_3908_ = l_Lean_Bool_toLBool(v___x_3907_);
v___x_3909_ = lean_box(v___x_3908_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3909_);
v___x_3911_ = v___x_3905_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3902_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3902_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3922_; lean_object* v_zero_3923_; uint8_t v_isZero_3924_; 
v_body_3922_ = lean_ctor_get(v_x_3888_, 2);
lean_inc_ref(v_body_3922_);
lean_dec_ref_known(v_x_3888_, 3);
v_zero_3923_ = lean_unsigned_to_nat(0u);
v_isZero_3924_ = lean_nat_dec_eq(v_x_3889_, v_zero_3923_);
if (v_isZero_3924_ == 1)
{
uint8_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec_ref(v_body_3922_);
lean_dec(v_x_3889_);
v___x_3925_ = 0;
v___x_3926_ = lean_box(v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
return v___x_3927_;
}
else
{
lean_object* v_one_3928_; lean_object* v_n_3929_; 
v_one_3928_ = lean_unsigned_to_nat(1u);
v_n_3929_ = lean_nat_sub(v_x_3889_, v_one_3928_);
lean_dec(v_x_3889_);
v_x_3888_ = v_body_3922_;
v_x_3889_ = v_n_3929_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3931_; 
v_body_3931_ = lean_ctor_get(v_x_3888_, 3);
lean_inc_ref(v_body_3931_);
lean_dec_ref_known(v_x_3888_, 4);
v_x_3888_ = v_body_3931_;
goto _start;
}
case 10:
{
lean_object* v_expr_3933_; 
v_expr_3933_ = lean_ctor_get(v_x_3888_, 1);
lean_inc_ref(v_expr_3933_);
lean_dec_ref_known(v_x_3888_, 2);
v_x_3888_ = v_expr_3933_;
goto _start;
}
default: 
{
lean_dec(v_x_3889_);
lean_dec_ref(v_x_3888_);
goto v___jp_3895_;
}
}
v___jp_3895_:
{
uint8_t v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = 2;
v___x_3897_ = lean_box(v___x_3896_);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3935_, lean_object* v_x_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3935_, v_x_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3943_, lean_object* v_x_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
switch(lean_obj_tag(v_x_3943_))
{
case 4:
{
lean_object* v_declName_3950_; lean_object* v_us_3951_; lean_object* v___x_3952_; 
v_declName_3950_ = lean_ctor_get(v_x_3943_, 0);
lean_inc(v_declName_3950_);
v_us_3951_ = lean_ctor_get(v_x_3943_, 1);
lean_inc(v_us_3951_);
lean_dec_ref_known(v_x_3943_, 2);
v___x_3952_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3950_, v_us_3951_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3953_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3954_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_x_3944_);
v_a_3955_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3952_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3952_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3963_; lean_object* v___x_3964_; 
v_fvarId_3963_ = lean_ctor_get(v_x_3943_, 0);
lean_inc(v_fvarId_3963_);
lean_dec_ref_known(v_x_3943_, 1);
v___x_3964_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3963_, v_a_3945_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3965_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3966_;
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_x_3944_);
v_a_3967_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3964_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3964_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3975_; lean_object* v___x_3976_; 
v_mvarId_3975_ = lean_ctor_get(v_x_3943_, 0);
lean_inc(v_mvarId_3975_);
lean_dec_ref_known(v_x_3943_, 1);
v___x_3976_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3975_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3977_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3978_;
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_x_3944_);
v_a_3979_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3976_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3976_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
case 5:
{
lean_object* v_fn_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_fn_3987_ = lean_ctor_get(v_x_3943_, 0);
lean_inc_ref(v_fn_3987_);
lean_dec_ref_known(v_x_3943_, 2);
v___x_3988_ = lean_unsigned_to_nat(1u);
v___x_3989_ = lean_nat_add(v_x_3944_, v___x_3988_);
lean_dec(v_x_3944_);
v_x_3943_ = v_fn_3987_;
v_x_3944_ = v___x_3989_;
goto _start;
}
case 10:
{
lean_object* v_expr_3991_; 
v_expr_3991_ = lean_ctor_get(v_x_3943_, 1);
lean_inc_ref(v_expr_3991_);
lean_dec_ref_known(v_x_3943_, 2);
v_x_3943_ = v_expr_3991_;
goto _start;
}
case 8:
{
lean_object* v_body_3993_; 
v_body_3993_ = lean_ctor_get(v_x_3943_, 3);
lean_inc_ref(v_body_3993_);
lean_dec_ref_known(v_x_3943_, 4);
v_x_3943_ = v_body_3993_;
goto _start;
}
case 6:
{
lean_object* v_body_3995_; lean_object* v_zero_3996_; uint8_t v_isZero_3997_; 
v_body_3995_ = lean_ctor_get(v_x_3943_, 2);
lean_inc_ref(v_body_3995_);
lean_dec_ref_known(v_x_3943_, 3);
v_zero_3996_ = lean_unsigned_to_nat(0u);
v_isZero_3997_ = lean_nat_dec_eq(v_x_3944_, v_zero_3996_);
if (v_isZero_3997_ == 1)
{
uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec_ref(v_body_3995_);
lean_dec(v_x_3944_);
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
v_n_4002_ = lean_nat_sub(v_x_3944_, v_one_4001_);
lean_dec(v_x_3944_);
v_x_3943_ = v_body_3995_;
v_x_3944_ = v_n_4002_;
goto _start;
}
}
default: 
{
uint8_t v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
lean_dec(v_x_3944_);
lean_dec_ref(v_x_3943_);
v___x_4004_ = 2;
v___x_4005_ = lean_box(v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4007_, lean_object* v_x_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4007_, v_x_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
switch(lean_obj_tag(v_x_4015_))
{
case 0:
{
uint8_t v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec_ref_known(v_x_4015_, 1);
v___x_4021_ = 2;
v___x_4022_ = lean_box(v___x_4021_);
v___x_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
return v___x_4023_;
}
case 1:
{
lean_object* v_fvarId_4024_; lean_object* v___x_4025_; 
v_fvarId_4024_ = lean_ctor_get(v_x_4015_, 0);
lean_inc(v_fvarId_4024_);
lean_dec_ref_known(v_x_4015_, 1);
v___x_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4024_, v_a_4016_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4026_, v___x_4027_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_a_4029_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4025_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4025_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4037_; lean_object* v___x_4038_; 
v_mvarId_4037_ = lean_ctor_get(v_x_4015_, 0);
lean_inc(v_mvarId_4037_);
lean_dec_ref_known(v_x_4015_, 1);
v___x_4038_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4037_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4039_, v___x_4040_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4038_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4038_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
case 4:
{
lean_object* v_declName_4050_; lean_object* v_us_4051_; lean_object* v___x_4052_; 
v_declName_4050_ = lean_ctor_get(v_x_4015_, 0);
lean_inc(v_declName_4050_);
v_us_4051_ = lean_ctor_get(v_x_4015_, 1);
lean_inc(v_us_4051_);
lean_dec_ref_known(v_x_4015_, 2);
v___x_4052_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4050_, v_us_4051_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4052_, 1);
v___x_4054_ = lean_unsigned_to_nat(0u);
v___x_4055_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4053_, v___x_4054_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4055_;
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v_a_4056_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4052_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4052_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
case 5:
{
lean_object* v_fn_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_fn_4064_ = lean_ctor_get(v_x_4015_, 0);
lean_inc_ref(v_fn_4064_);
lean_dec_ref_known(v_x_4015_, 2);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4064_, v___x_4065_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4066_;
}
case 7:
{
lean_object* v_body_4067_; 
v_body_4067_ = lean_ctor_get(v_x_4015_, 2);
lean_inc_ref(v_body_4067_);
lean_dec_ref_known(v_x_4015_, 3);
v_x_4015_ = v_body_4067_;
goto _start;
}
case 8:
{
lean_object* v_body_4069_; 
v_body_4069_ = lean_ctor_get(v_x_4015_, 3);
lean_inc_ref(v_body_4069_);
lean_dec_ref_known(v_x_4015_, 4);
v_x_4015_ = v_body_4069_;
goto _start;
}
case 10:
{
lean_object* v_expr_4071_; 
v_expr_4071_ = lean_ctor_get(v_x_4015_, 1);
lean_inc_ref(v_expr_4071_);
lean_dec_ref_known(v_x_4015_, 2);
v_x_4015_ = v_expr_4071_;
goto _start;
}
case 11:
{
uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec_ref_known(v_x_4015_, 3);
v___x_4073_ = 2;
v___x_4074_ = lean_box(v___x_4073_);
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
}
default: 
{
uint8_t v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec_ref(v_x_4015_);
v___x_4076_ = 0;
v___x_4077_ = lean_box(v___x_4076_);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Lean_Meta_isPropQuick(v_x_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4092_; 
lean_inc_ref(v_e_4086_);
v___x_4092_ = l_Lean_Meta_isPropQuick(v_e_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4149_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4149_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4149_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
uint8_t v___x_4097_; 
v___x_4097_ = lean_unbox(v_a_4093_);
lean_dec(v_a_4093_);
switch(v___x_4097_)
{
case 0:
{
uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec_ref(v_e_4086_);
v___x_4098_ = 0;
v___x_4099_ = lean_box(v___x_4098_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4099_);
v___x_4101_ = v___x_4095_;
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
case 1:
{
uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
lean_dec_ref(v_e_4086_);
v___x_4103_ = 1;
v___x_4104_ = lean_box(v___x_4103_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4104_);
v___x_4106_ = v___x_4095_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
default: 
{
lean_object* v___x_4108_; 
lean_del_object(v___x_4095_);
lean_inc(v_a_4090_);
lean_inc_ref(v_a_4089_);
lean_inc(v_a_4088_);
lean_inc_ref(v_a_4087_);
v___x_4108_ = lean_infer_type(v_e_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = l_Lean_Meta_whnfD(v_a_4109_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4132_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4132_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4132_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
if (lean_obj_tag(v_a_4111_) == 3)
{
lean_object* v_u_4115_; lean_object* v___x_4116_; lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
lean_del_object(v___x_4113_);
v_u_4115_ = lean_ctor_get(v_a_4111_, 0);
lean_inc(v_u_4115_);
lean_dec_ref_known(v_a_4111_, 1);
v___x_4116_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4115_, v_a_4088_);
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
uint8_t v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v___x_4121_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4117_);
lean_dec(v_a_4117_);
v___x_4122_ = lean_box(v___x_4121_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v___x_4122_);
v___x_4124_ = v___x_4119_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
else
{
uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
lean_dec(v_a_4111_);
v___x_4127_ = 0;
v___x_4128_ = lean_box(v___x_4127_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4128_);
v___x_4130_ = v___x_4113_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_a_4133_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4110_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4110_);
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
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
v_a_4141_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4108_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4108_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v_e_4086_);
v_a_4150_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4092_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4092_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Meta_isProp(v_e_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4165_){
_start:
{
switch(lean_obj_tag(v_x_4165_))
{
case 0:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_unsigned_to_nat(0u);
return v___x_4166_;
}
case 1:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
return v___x_4167_;
}
case 2:
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_unsigned_to_nat(2u);
return v___x_4168_;
}
default: 
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_unsigned_to_nat(3u);
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4170_);
lean_dec(v_x_4170_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4172_, lean_object* v_k_4173_){
_start:
{
if (lean_obj_tag(v_t_4172_) == 3)
{
lean_object* v_idx_4174_; lean_object* v___x_4175_; 
v_idx_4174_ = lean_ctor_get(v_t_4172_, 0);
lean_inc(v_idx_4174_);
lean_dec_ref_known(v_t_4172_, 1);
v___x_4175_ = lean_apply_1(v_k_4173_, v_idx_4174_);
return v___x_4175_;
}
else
{
lean_dec(v_t_4172_);
return v_k_4173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4176_, lean_object* v_ctorIdx_4177_, lean_object* v_t_4178_, lean_object* v_h_4179_, lean_object* v_k_4180_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4178_, v_k_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4182_, lean_object* v_ctorIdx_4183_, lean_object* v_t_4184_, lean_object* v_h_4185_, lean_object* v_k_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4182_, v_ctorIdx_4183_, v_t_4184_, v_h_4185_, v_k_4186_);
lean_dec(v_ctorIdx_4183_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4188_, lean_object* v_false_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4188_, v_false_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4191_, lean_object* v_t_4192_, lean_object* v_h_4193_, lean_object* v_false_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4192_, v_false_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4196_, lean_object* v_true_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4196_, v_true_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4199_, lean_object* v_t_4200_, lean_object* v_h_4201_, lean_object* v_true_4202_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4200_, v_true_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4204_, lean_object* v_undef_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4204_, v_undef_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4207_, lean_object* v_t_4208_, lean_object* v_h_4209_, lean_object* v_undef_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4208_, v_undef_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4212_, lean_object* v_bvar_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4212_, v_bvar_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4215_, lean_object* v_t_4216_, lean_object* v_h_4217_, lean_object* v_bvar_4218_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4216_, v_bvar_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4220_){
_start:
{
switch(v_x_4220_)
{
case 0:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_box(0);
return v___x_4221_;
}
case 1:
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_box(1);
return v___x_4222_;
}
default: 
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(2);
return v___x_4223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4224_){
_start:
{
uint8_t v_x_25__boxed_4225_; lean_object* v_res_4226_; 
v_x_25__boxed_4225_ = lean_unbox(v_x_4224_);
v_res_4226_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4225_);
return v_res_4226_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4227_){
_start:
{
switch(lean_obj_tag(v_x_4227_))
{
case 0:
{
uint8_t v___x_4228_; 
v___x_4228_ = 0;
return v___x_4228_;
}
case 1:
{
uint8_t v___x_4229_; 
v___x_4229_ = 1;
return v___x_4229_;
}
default: 
{
uint8_t v___x_4230_; 
v___x_4230_ = 2;
return v___x_4230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4231_){
_start:
{
uint8_t v_res_4232_; lean_object* v_r_4233_; 
v_res_4232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4231_);
lean_dec(v_x_4231_);
v_r_4233_ = lean_box(v_res_4232_);
return v_r_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4235_){
_start:
{
switch(lean_obj_tag(v_e_4235_))
{
case 3:
{
lean_object* v_u_4236_; uint8_t v___x_4237_; 
v_u_4236_ = lean_ctor_get(v_e_4235_, 0);
v___x_4237_ = l_Lean_Level_isNeverZero(v_u_4236_);
if (v___x_4237_ == 0)
{
uint8_t v___x_4238_; 
v___x_4238_ = l_Lean_Level_isZero(v_u_4236_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_box(2);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_box(1);
return v___x_4240_;
}
}
else
{
lean_object* v___x_4241_; 
v___x_4241_ = lean_box(0);
return v___x_4241_;
}
}
case 5:
{
lean_object* v_fn_4242_; 
v_fn_4242_ = lean_ctor_get(v_e_4235_, 0);
if (lean_obj_tag(v_fn_4242_) == 4)
{
lean_object* v_declName_4243_; 
v_declName_4243_ = lean_ctor_get(v_fn_4242_, 0);
if (lean_obj_tag(v_declName_4243_) == 1)
{
lean_object* v_pre_4244_; 
v_pre_4244_ = lean_ctor_get(v_declName_4243_, 0);
if (lean_obj_tag(v_pre_4244_) == 0)
{
lean_object* v_arg_4245_; lean_object* v_str_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v_arg_4245_ = lean_ctor_get(v_e_4235_, 1);
v_str_4246_ = lean_ctor_get(v_declName_4243_, 1);
v___x_4247_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4248_ = lean_string_dec_eq(v_str_4246_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_box(2);
return v___x_4249_;
}
else
{
v_e_4235_ = v_arg_4245_;
goto _start;
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
else
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_box(2);
return v___x_4253_;
}
}
default: 
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_box(2);
return v___x_4254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4255_);
lean_dec_ref(v_e_4255_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4257_, lean_object* v_binderType_4258_){
_start:
{
if (lean_obj_tag(v_r_4257_) == 3)
{
lean_object* v_idx_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4271_; 
v_idx_4259_ = lean_ctor_get(v_r_4257_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_r_4257_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4261_ = v_r_4257_;
v_isShared_4262_ = v_isSharedCheck_4271_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_idx_4259_);
lean_dec(v_r_4257_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4271_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v_zero_4263_; uint8_t v_isZero_4264_; 
v_zero_4263_ = lean_unsigned_to_nat(0u);
v_isZero_4264_ = lean_nat_dec_eq(v_idx_4259_, v_zero_4263_);
if (v_isZero_4264_ == 1)
{
lean_object* v___x_4265_; 
lean_del_object(v___x_4261_);
lean_dec(v_idx_4259_);
v___x_4265_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4258_);
return v___x_4265_;
}
else
{
lean_object* v_one_4266_; lean_object* v_n_4267_; lean_object* v___x_4269_; 
v_one_4266_ = lean_unsigned_to_nat(1u);
v_n_4267_ = lean_nat_sub(v_idx_4259_, v_one_4266_);
lean_dec(v_idx_4259_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v_n_4267_);
v___x_4269_ = v___x_4261_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_n_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
return v_r_4257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4272_, lean_object* v_binderType_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4272_, v_binderType_4273_);
lean_dec_ref(v_binderType_4273_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4275_, lean_object* v_x_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_type_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; 
switch(lean_obj_tag(v_x_4275_))
{
case 7:
{
lean_object* v_binderType_4310_; lean_object* v_body_4311_; lean_object* v_zero_4312_; uint8_t v_isZero_4313_; 
v_binderType_4310_ = lean_ctor_get(v_x_4275_, 1);
v_body_4311_ = lean_ctor_get(v_x_4275_, 2);
v_zero_4312_ = lean_unsigned_to_nat(0u);
v_isZero_4313_ = lean_nat_dec_eq(v_x_4276_, v_zero_4312_);
if (v_isZero_4313_ == 1)
{
v_type_4283_ = v_x_4275_;
v___y_4284_ = v_a_4277_;
v___y_4285_ = v_a_4278_;
v___y_4286_ = v_a_4279_;
v___y_4287_ = v_a_4280_;
goto v___jp_4282_;
}
else
{
lean_object* v_one_4314_; lean_object* v_n_4315_; lean_object* v___x_4316_; 
lean_inc_ref(v_body_4311_);
lean_inc_ref(v_binderType_4310_);
lean_dec_ref_known(v_x_4275_, 3);
v_one_4314_ = lean_unsigned_to_nat(1u);
v_n_4315_ = lean_nat_sub(v_x_4276_, v_one_4314_);
v___x_4316_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4311_, v_n_4315_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_n_4315_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4325_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4319_ = v___x_4316_;
v_isShared_4320_ = v_isSharedCheck_4325_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4316_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4325_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
v___x_4321_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4317_, v_binderType_4310_);
lean_dec_ref(v_binderType_4310_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 0, v___x_4321_);
v___x_4323_ = v___x_4319_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
else
{
lean_dec_ref(v_binderType_4310_);
return v___x_4316_;
}
}
}
case 8:
{
lean_object* v_type_4326_; lean_object* v_body_4327_; lean_object* v___x_4328_; 
v_type_4326_ = lean_ctor_get(v_x_4275_, 1);
lean_inc_ref(v_type_4326_);
v_body_4327_ = lean_ctor_get(v_x_4275_, 3);
lean_inc_ref(v_body_4327_);
lean_dec_ref_known(v_x_4275_, 4);
v___x_4328_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4327_, v_x_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4337_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4337_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4329_, v_type_4326_);
lean_dec_ref(v_type_4326_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v___x_4333_);
v___x_4335_ = v___x_4331_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
else
{
lean_dec_ref(v_type_4326_);
return v___x_4328_;
}
}
case 10:
{
lean_object* v_expr_4338_; 
v_expr_4338_ = lean_ctor_get(v_x_4275_, 1);
lean_inc_ref(v_expr_4338_);
lean_dec_ref_known(v_x_4275_, 2);
v_x_4275_ = v_expr_4338_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_deBruijnIndex_4340_ = lean_ctor_get(v_x_4275_, 0);
lean_inc(v_deBruijnIndex_4340_);
lean_dec_ref_known(v_x_4275_, 1);
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = lean_nat_dec_eq(v_x_4276_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec(v_deBruijnIndex_4340_);
goto v___jp_4307_;
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4343_, 0, v_deBruijnIndex_4340_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
return v___x_4344_;
}
}
default: 
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_nat_dec_eq(v_x_4276_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_dec_ref(v_x_4275_);
goto v___jp_4307_;
}
else
{
v_type_4283_ = v_x_4275_;
v___y_4284_ = v_a_4277_;
v___y_4285_ = v_a_4278_;
v___y_4286_ = v_a_4279_;
v___y_4287_ = v_a_4280_;
goto v___jp_4282_;
}
}
}
v___jp_4282_:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Meta_isPropQuick(v_type_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4298_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4298_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4298_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4296_; 
v___x_4293_ = lean_unbox(v_a_4289_);
lean_dec(v_a_4289_);
v___x_4294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4293_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4294_);
v___x_4296_ = v___x_4291_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4299_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4288_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4288_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
v___jp_4307_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_box(2);
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4347_, v_x_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_x_4348_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4355_, lean_object* v_n_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4355_, v_n_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4372_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4372_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4372_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4367_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4363_);
lean_dec(v_a_4363_);
v___x_4368_ = lean_box(v___x_4367_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4368_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
v_a_4373_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4362_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4362_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4381_, lean_object* v_n_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4381_, v_n_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_n_4382_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4389_, lean_object* v_x_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
switch(lean_obj_tag(v_x_4389_))
{
case 4:
{
lean_object* v_declName_4396_; lean_object* v_us_4397_; lean_object* v___x_4398_; 
v_declName_4396_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_declName_4396_);
v_us_4397_ = lean_ctor_get(v_x_4389_, 1);
lean_inc(v_us_4397_);
lean_dec_ref_known(v_x_4389_, 2);
v___x_4398_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4396_, v_us_4397_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4399_, v_x_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_x_4390_);
return v___x_4400_;
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_x_4390_);
v_a_4401_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4398_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4398_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4409_; lean_object* v___x_4410_; 
v_fvarId_4409_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_fvarId_4409_);
lean_dec_ref_known(v_x_4389_, 1);
v___x_4410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4409_, v_a_4391_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4411_, v_x_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_x_4390_);
return v___x_4412_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_x_4390_);
v_a_4413_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4410_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4410_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4421_; lean_object* v___x_4422_; 
v_mvarId_4421_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_mvarId_4421_);
lean_dec_ref_known(v_x_4389_, 1);
v___x_4422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4421_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4424_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4422_, 1);
v___x_4424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4423_, v_x_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_x_4390_);
return v___x_4424_;
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_x_4390_);
v_a_4425_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4422_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4422_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
case 5:
{
lean_object* v_fn_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_fn_4433_ = lean_ctor_get(v_x_4389_, 0);
lean_inc_ref(v_fn_4433_);
lean_dec_ref_known(v_x_4389_, 2);
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_nat_add(v_x_4390_, v___x_4434_);
lean_dec(v_x_4390_);
v_x_4389_ = v_fn_4433_;
v_x_4390_ = v___x_4435_;
goto _start;
}
case 10:
{
lean_object* v_expr_4437_; 
v_expr_4437_ = lean_ctor_get(v_x_4389_, 1);
lean_inc_ref(v_expr_4437_);
lean_dec_ref_known(v_x_4389_, 2);
v_x_4389_ = v_expr_4437_;
goto _start;
}
case 8:
{
lean_object* v_body_4439_; 
v_body_4439_ = lean_ctor_get(v_x_4389_, 3);
lean_inc_ref(v_body_4439_);
lean_dec_ref_known(v_x_4389_, 4);
v_x_4389_ = v_body_4439_;
goto _start;
}
case 6:
{
lean_object* v_body_4441_; lean_object* v_zero_4442_; uint8_t v_isZero_4443_; 
v_body_4441_ = lean_ctor_get(v_x_4389_, 2);
lean_inc_ref(v_body_4441_);
lean_dec_ref_known(v_x_4389_, 3);
v_zero_4442_ = lean_unsigned_to_nat(0u);
v_isZero_4443_ = lean_nat_dec_eq(v_x_4390_, v_zero_4442_);
if (v_isZero_4443_ == 1)
{
lean_object* v___x_4444_; 
lean_dec(v_x_4390_);
v___x_4444_ = l_Lean_Meta_isProofQuick(v_body_4441_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
return v___x_4444_;
}
else
{
lean_object* v_one_4445_; lean_object* v_n_4446_; 
v_one_4445_ = lean_unsigned_to_nat(1u);
v_n_4446_ = lean_nat_sub(v_x_4390_, v_one_4445_);
lean_dec(v_x_4390_);
v_x_4389_ = v_body_4441_;
v_x_4390_ = v_n_4446_;
goto _start;
}
}
default: 
{
uint8_t v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec(v_x_4390_);
lean_dec_ref(v_x_4389_);
v___x_4448_ = 2;
v___x_4449_ = lean_box(v___x_4448_);
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
switch(lean_obj_tag(v_x_4451_))
{
case 0:
{
uint8_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec_ref_known(v_x_4451_, 1);
v___x_4457_ = 2;
v___x_4458_ = lean_box(v___x_4457_);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
case 1:
{
lean_object* v_fvarId_4460_; lean_object* v___x_4461_; 
v_fvarId_4460_ = lean_ctor_get(v_x_4451_, 0);
lean_inc(v_fvarId_4460_);
lean_dec_ref_known(v_x_4451_, 1);
v___x_4461_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4460_, v_a_4452_, v_a_4454_, v_a_4455_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
v___x_4463_ = lean_unsigned_to_nat(0u);
v___x_4464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4462_, v___x_4463_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4464_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4461_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4461_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4473_; lean_object* v___x_4474_; 
v_mvarId_4473_ = lean_ctor_get(v_x_4451_, 0);
lean_inc(v_mvarId_4473_);
lean_dec_ref_known(v_x_4451_, 1);
v___x_4474_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4473_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = lean_unsigned_to_nat(0u);
v___x_4477_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4475_, v___x_4476_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4477_;
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
v_a_4478_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4474_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4474_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
case 4:
{
lean_object* v_declName_4486_; lean_object* v_us_4487_; lean_object* v___x_4488_; 
v_declName_4486_ = lean_ctor_get(v_x_4451_, 0);
lean_inc(v_declName_4486_);
v_us_4487_ = lean_ctor_get(v_x_4451_, 1);
lean_inc(v_us_4487_);
lean_dec_ref_known(v_x_4451_, 2);
v___x_4488_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4486_, v_us_4487_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = lean_unsigned_to_nat(0u);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4489_, v___x_4490_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
v_a_4492_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4488_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4488_);
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
v_fn_4500_ = lean_ctor_get(v_x_4451_, 0);
lean_inc_ref(v_fn_4500_);
lean_dec_ref_known(v_x_4451_, 2);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4500_, v___x_4501_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_);
return v___x_4502_;
}
case 6:
{
lean_object* v_body_4503_; 
v_body_4503_ = lean_ctor_get(v_x_4451_, 2);
lean_inc_ref(v_body_4503_);
lean_dec_ref_known(v_x_4451_, 3);
v_x_4451_ = v_body_4503_;
goto _start;
}
case 8:
{
lean_object* v_body_4505_; 
v_body_4505_ = lean_ctor_get(v_x_4451_, 3);
lean_inc_ref(v_body_4505_);
lean_dec_ref_known(v_x_4451_, 4);
v_x_4451_ = v_body_4505_;
goto _start;
}
case 10:
{
lean_object* v_expr_4507_; 
v_expr_4507_ = lean_ctor_get(v_x_4451_, 1);
lean_inc_ref(v_expr_4507_);
lean_dec_ref_known(v_x_4451_, 2);
v_x_4451_ = v_expr_4507_;
goto _start;
}
case 11:
{
uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref_known(v_x_4451_, 3);
v___x_4509_ = 2;
v___x_4510_ = lean_box(v___x_4509_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
default: 
{
uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_dec_ref(v_x_4451_);
v___x_4512_ = 0;
v___x_4513_ = lean_box(v___x_4512_);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_Meta_isProofQuick(v_x_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4522_, lean_object* v_x_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4522_, v_x_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v___x_4536_; 
lean_inc_ref(v_e_4530_);
v___x_4536_ = l_Lean_Meta_isProofQuick(v_e_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4563_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4563_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4563_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
uint8_t v___x_4541_; 
v___x_4541_ = lean_unbox(v_a_4537_);
lean_dec(v_a_4537_);
switch(v___x_4541_)
{
case 0:
{
uint8_t v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4545_; 
lean_dec_ref(v_e_4530_);
v___x_4542_ = 0;
v___x_4543_ = lean_box(v___x_4542_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4543_);
v___x_4545_ = v___x_4539_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
case 1:
{
uint8_t v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
lean_dec_ref(v_e_4530_);
v___x_4547_ = 1;
v___x_4548_ = lean_box(v___x_4547_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4548_);
v___x_4550_ = v___x_4539_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
default: 
{
lean_object* v___x_4552_; 
lean_del_object(v___x_4539_);
lean_inc(v_a_4534_);
lean_inc_ref(v_a_4533_);
lean_inc(v_a_4532_);
lean_inc_ref(v_a_4531_);
v___x_4552_ = lean_infer_type(v_e_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4554_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4552_, 1);
v___x_4554_ = l_Lean_Meta_isProp(v_a_4553_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
v_a_4555_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4552_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4552_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec_ref(v_e_4530_);
v_a_4564_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4536_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4536_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_Meta_isProof(v_e_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4579_, lean_object* v_x_4580_){
_start:
{
switch(lean_obj_tag(v_x_4579_))
{
case 3:
{
lean_object* v___x_4586_; uint8_t v___x_4587_; 
v___x_4586_ = lean_unsigned_to_nat(0u);
v___x_4587_ = lean_nat_dec_eq(v_x_4580_, v___x_4586_);
lean_dec(v_x_4580_);
if (v___x_4587_ == 0)
{
goto v___jp_4582_;
}
else
{
uint8_t v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = 1;
v___x_4589_ = lean_box(v___x_4588_);
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
return v___x_4590_;
}
}
case 7:
{
lean_object* v_body_4591_; lean_object* v_zero_4592_; uint8_t v_isZero_4593_; 
v_body_4591_ = lean_ctor_get(v_x_4579_, 2);
v_zero_4592_ = lean_unsigned_to_nat(0u);
v_isZero_4593_ = lean_nat_dec_eq(v_x_4580_, v_zero_4592_);
if (v_isZero_4593_ == 1)
{
uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_dec(v_x_4580_);
v___x_4594_ = 0;
v___x_4595_ = lean_box(v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
else
{
lean_object* v_one_4597_; lean_object* v_n_4598_; 
v_one_4597_ = lean_unsigned_to_nat(1u);
v_n_4598_ = lean_nat_sub(v_x_4580_, v_one_4597_);
lean_dec(v_x_4580_);
v_x_4579_ = v_body_4591_;
v_x_4580_ = v_n_4598_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4600_; 
v_body_4600_ = lean_ctor_get(v_x_4579_, 3);
v_x_4579_ = v_body_4600_;
goto _start;
}
case 10:
{
lean_object* v_expr_4602_; 
v_expr_4602_ = lean_ctor_get(v_x_4579_, 1);
v_x_4579_ = v_expr_4602_;
goto _start;
}
default: 
{
lean_dec(v_x_4580_);
goto v___jp_4582_;
}
}
v___jp_4582_:
{
uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = 2;
v___x_4584_ = lean_box(v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4604_, lean_object* v_x_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4604_, v_x_4605_);
lean_dec_ref(v_x_4604_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4608_, lean_object* v_x_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4608_, v_x_4609_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4616_, lean_object* v_x_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4616_, v_x_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec_ref(v_x_4616_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4624_, lean_object* v_x_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
switch(lean_obj_tag(v_x_4624_))
{
case 4:
{
lean_object* v_declName_4631_; lean_object* v_us_4632_; lean_object* v___x_4633_; 
v_declName_4631_ = lean_ctor_get(v_x_4624_, 0);
lean_inc(v_declName_4631_);
v_us_4632_ = lean_ctor_get(v_x_4624_, 1);
lean_inc(v_us_4632_);
lean_dec_ref_known(v_x_4624_, 2);
v___x_4633_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4631_, v_us_4632_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4635_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref_known(v___x_4633_, 1);
v___x_4635_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4634_, v_x_4625_);
lean_dec(v_a_4634_);
return v___x_4635_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_x_4625_);
v_a_4636_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4633_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4633_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4644_; lean_object* v___x_4645_; 
v_fvarId_4644_ = lean_ctor_get(v_x_4624_, 0);
lean_inc(v_fvarId_4644_);
lean_dec_ref_known(v_x_4624_, 1);
v___x_4645_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4644_, v_a_4626_, v_a_4628_, v_a_4629_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4646_, v_x_4625_);
lean_dec(v_a_4646_);
return v___x_4647_;
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_dec(v_x_4625_);
v_a_4648_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4645_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4645_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4656_; lean_object* v___x_4657_; 
v_mvarId_4656_ = lean_ctor_get(v_x_4624_, 0);
lean_inc(v_mvarId_4656_);
lean_dec_ref_known(v_x_4624_, 1);
v___x_4657_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4656_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4659_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v___x_4657_, 1);
v___x_4659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4658_, v_x_4625_);
lean_dec(v_a_4658_);
return v___x_4659_;
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v_x_4625_);
v_a_4660_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4657_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4657_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
case 5:
{
lean_object* v_fn_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_fn_4668_ = lean_ctor_get(v_x_4624_, 0);
lean_inc_ref(v_fn_4668_);
lean_dec_ref_known(v_x_4624_, 2);
v___x_4669_ = lean_unsigned_to_nat(1u);
v___x_4670_ = lean_nat_add(v_x_4625_, v___x_4669_);
lean_dec(v_x_4625_);
v_x_4624_ = v_fn_4668_;
v_x_4625_ = v___x_4670_;
goto _start;
}
case 10:
{
lean_object* v_expr_4672_; 
v_expr_4672_ = lean_ctor_get(v_x_4624_, 1);
lean_inc_ref(v_expr_4672_);
lean_dec_ref_known(v_x_4624_, 2);
v_x_4624_ = v_expr_4672_;
goto _start;
}
case 8:
{
lean_object* v_body_4674_; 
v_body_4674_ = lean_ctor_get(v_x_4624_, 3);
lean_inc_ref(v_body_4674_);
lean_dec_ref_known(v_x_4624_, 4);
v_x_4624_ = v_body_4674_;
goto _start;
}
case 6:
{
lean_object* v_body_4676_; lean_object* v_zero_4677_; uint8_t v_isZero_4678_; 
v_body_4676_ = lean_ctor_get(v_x_4624_, 2);
lean_inc_ref(v_body_4676_);
lean_dec_ref_known(v_x_4624_, 3);
v_zero_4677_ = lean_unsigned_to_nat(0u);
v_isZero_4678_ = lean_nat_dec_eq(v_x_4625_, v_zero_4677_);
if (v_isZero_4678_ == 1)
{
uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_dec_ref(v_body_4676_);
lean_dec(v_x_4625_);
v___x_4679_ = 0;
v___x_4680_ = lean_box(v___x_4679_);
v___x_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
return v___x_4681_;
}
else
{
lean_object* v_one_4682_; lean_object* v_n_4683_; 
v_one_4682_ = lean_unsigned_to_nat(1u);
v_n_4683_ = lean_nat_sub(v_x_4625_, v_one_4682_);
lean_dec(v_x_4625_);
v_x_4624_ = v_body_4676_;
v_x_4625_ = v_n_4683_;
goto _start;
}
}
default: 
{
uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
lean_dec(v_x_4625_);
lean_dec_ref(v_x_4624_);
v___x_4685_ = 2;
v___x_4686_ = lean_box(v___x_4685_);
v___x_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
return v___x_4687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4688_, lean_object* v_x_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4688_, v_x_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
switch(lean_obj_tag(v_x_4696_))
{
case 1:
{
lean_object* v_fvarId_4702_; lean_object* v___x_4703_; 
v_fvarId_4702_ = lean_ctor_get(v_x_4696_, 0);
lean_inc(v_fvarId_4702_);
lean_dec_ref_known(v_x_4696_, 1);
v___x_4703_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4702_, v_a_4697_, v_a_4699_, v_a_4700_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4703_, 1);
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4704_, v___x_4705_);
lean_dec(v_a_4704_);
return v___x_4706_;
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
v_a_4707_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___x_4703_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4703_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4715_; lean_object* v___x_4716_; 
v_mvarId_4715_ = lean_ctor_get(v_x_4696_, 0);
lean_inc(v_mvarId_4715_);
lean_dec_ref_known(v_x_4696_, 1);
v___x_4716_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4715_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v___x_4718_ = lean_unsigned_to_nat(0u);
v___x_4719_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4717_, v___x_4718_);
lean_dec(v_a_4717_);
return v___x_4719_;
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_a_4720_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4716_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4716_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
case 3:
{
uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
lean_dec_ref_known(v_x_4696_, 1);
v___x_4728_ = 1;
v___x_4729_ = lean_box(v___x_4728_);
v___x_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
return v___x_4730_;
}
case 4:
{
lean_object* v_declName_4731_; lean_object* v_us_4732_; lean_object* v___x_4733_; 
v_declName_4731_ = lean_ctor_get(v_x_4696_, 0);
lean_inc(v_declName_4731_);
v_us_4732_ = lean_ctor_get(v_x_4696_, 1);
lean_inc(v_us_4732_);
lean_dec_ref_known(v_x_4696_, 2);
v___x_4733_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4731_, v_us_4732_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
v___x_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4734_, v___x_4735_);
lean_dec(v_a_4734_);
return v___x_4736_;
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_a_4737_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4733_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4733_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
case 5:
{
lean_object* v_fn_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_fn_4745_ = lean_ctor_get(v_x_4696_, 0);
lean_inc_ref(v_fn_4745_);
lean_dec_ref_known(v_x_4696_, 2);
v___x_4746_ = lean_unsigned_to_nat(1u);
v___x_4747_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4745_, v___x_4746_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_);
return v___x_4747_;
}
case 6:
{
uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_dec_ref_known(v_x_4696_, 3);
v___x_4748_ = 0;
v___x_4749_ = lean_box(v___x_4748_);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
case 7:
{
uint8_t v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
lean_dec_ref_known(v_x_4696_, 3);
v___x_4751_ = 1;
v___x_4752_ = lean_box(v___x_4751_);
v___x_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
return v___x_4753_;
}
case 8:
{
lean_object* v_body_4754_; 
v_body_4754_ = lean_ctor_get(v_x_4696_, 3);
lean_inc_ref(v_body_4754_);
lean_dec_ref_known(v_x_4696_, 4);
v_x_4696_ = v_body_4754_;
goto _start;
}
case 9:
{
uint8_t v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
lean_dec_ref_known(v_x_4696_, 1);
v___x_4756_ = 0;
v___x_4757_ = lean_box(v___x_4756_);
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4757_);
return v___x_4758_;
}
case 10:
{
lean_object* v_expr_4759_; 
v_expr_4759_ = lean_ctor_get(v_x_4696_, 1);
lean_inc_ref(v_expr_4759_);
lean_dec_ref_known(v_x_4696_, 2);
v_x_4696_ = v_expr_4759_;
goto _start;
}
default: 
{
uint8_t v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
lean_dec_ref(v_x_4696_);
v___x_4761_ = 2;
v___x_4762_ = lean_box(v___x_4761_);
v___x_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
return v___x_4763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_Meta_isTypeQuick(v_x_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v___x_4777_; 
lean_inc_ref(v_e_4771_);
v___x_4777_ = l_Lean_Meta_isTypeQuick(v_e_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4827_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4827_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4827_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
uint8_t v___x_4782_; 
v___x_4782_ = lean_unbox(v_a_4778_);
lean_dec(v_a_4778_);
switch(v___x_4782_)
{
case 0:
{
uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4786_; 
lean_dec_ref(v_e_4771_);
v___x_4783_ = 0;
v___x_4784_ = lean_box(v___x_4783_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4784_);
v___x_4786_ = v___x_4780_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
case 1:
{
uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
lean_dec_ref(v_e_4771_);
v___x_4788_ = 1;
v___x_4789_ = lean_box(v___x_4788_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4789_);
v___x_4791_ = v___x_4780_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
default: 
{
lean_object* v___x_4793_; 
lean_del_object(v___x_4780_);
lean_inc(v_a_4775_);
lean_inc_ref(v_a_4774_);
lean_inc(v_a_4773_);
lean_inc_ref(v_a_4772_);
v___x_4793_ = lean_infer_type(v_e_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4795_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v___x_4795_ = l_Lean_Meta_whnfD(v_a_4794_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4810_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4798_ = v___x_4795_;
v_isShared_4799_ = v_isSharedCheck_4810_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4795_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4810_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
if (lean_obj_tag(v_a_4796_) == 3)
{
uint8_t v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4803_; 
lean_dec_ref_known(v_a_4796_, 1);
v___x_4800_ = 1;
v___x_4801_ = lean_box(v___x_4800_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 0, v___x_4801_);
v___x_4803_ = v___x_4798_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
else
{
uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_dec(v_a_4796_);
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 0, v___x_4806_);
v___x_4808_ = v___x_4798_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
v_a_4811_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4795_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4795_);
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
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_a_4819_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4793_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4793_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec_ref(v_e_4771_);
v_a_4828_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4777_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4777_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_Meta_isType(v_e_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4843_){
_start:
{
switch(lean_obj_tag(v_x_4843_))
{
case 7:
{
lean_object* v_body_4844_; 
v_body_4844_ = lean_ctor_get(v_x_4843_, 2);
v_x_4843_ = v_body_4844_;
goto _start;
}
case 3:
{
lean_object* v_u_4846_; lean_object* v___x_4847_; 
v_u_4846_ = lean_ctor_get(v_x_4843_, 0);
lean_inc(v_u_4846_);
v___x_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4847_, 0, v_u_4846_);
return v___x_4847_;
}
default: 
{
lean_object* v___x_4848_; 
v___x_4848_ = lean_box(0);
return v___x_4848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4849_);
lean_dec_ref(v_x_4849_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4851_, lean_object* v_body_4852_, lean_object* v_x_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4851_, v_body_4852_, v_x_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4862_, lean_object* v_xs_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
switch(lean_obj_tag(v_type_4862_))
{
case 3:
{
lean_object* v_u_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref(v_xs_4863_);
v_u_4869_ = lean_ctor_get(v_type_4862_, 0);
lean_inc(v_u_4869_);
lean_dec_ref_known(v_type_4862_, 1);
v___x_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4870_, 0, v_u_4869_);
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
return v___x_4871_;
}
case 7:
{
lean_object* v_binderName_4872_; lean_object* v_binderType_4873_; lean_object* v_body_4874_; uint8_t v_binderInfo_4875_; lean_object* v___f_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v_binderName_4872_ = lean_ctor_get(v_type_4862_, 0);
lean_inc(v_binderName_4872_);
v_binderType_4873_ = lean_ctor_get(v_type_4862_, 1);
lean_inc_ref(v_binderType_4873_);
v_body_4874_ = lean_ctor_get(v_type_4862_, 2);
lean_inc_ref(v_body_4874_);
v_binderInfo_4875_ = lean_ctor_get_uint8(v_type_4862_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4862_, 3);
lean_inc_ref(v_xs_4863_);
v___f_4876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4876_, 0, v_xs_4863_);
lean_closure_set(v___f_4876_, 1, v_body_4874_);
v___x_4877_ = lean_expr_instantiate_rev(v_binderType_4873_, v_xs_4863_);
lean_dec_ref(v_xs_4863_);
lean_dec_ref(v_binderType_4873_);
v___x_4878_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4872_, v_binderInfo_4875_, v___x_4877_, v___f_4876_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
return v___x_4878_;
}
default: 
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_expr_instantiate_rev(v_type_4862_, v_xs_4863_);
lean_dec_ref(v_xs_4863_);
lean_dec_ref(v_type_4862_);
v___x_4880_ = l_Lean_Meta_whnfD(v___x_4879_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4896_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4896_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4896_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
switch(lean_obj_tag(v_a_4881_))
{
case 3:
{
lean_object* v_u_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v_u_4885_ = lean_ctor_get(v_a_4881_, 0);
lean_inc(v_u_4885_);
lean_dec_ref_known(v_a_4881_, 1);
v___x_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4886_, 0, v_u_4885_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4886_);
v___x_4888_ = v___x_4883_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
case 7:
{
lean_object* v___x_4890_; 
lean_del_object(v___x_4883_);
v___x_4890_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4862_ = v_a_4881_;
v_xs_4863_ = v___x_4890_;
goto _start;
}
default: 
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_dec(v_a_4881_);
v___x_4892_ = lean_box(0);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4892_);
v___x_4894_ = v___x_4883_;
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
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4880_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4880_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4905_, lean_object* v_body_4906_, lean_object* v_x_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4913_ = lean_array_push(v_xs_4905_, v_x_4907_);
v___x_4914_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4906_, v___x_4913_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4915_, lean_object* v_xs_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4915_, v_xs_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4923_, lean_object* v_cache_4924_, lean_object* v_a_x3f_4925_){
_start:
{
lean_object* v___x_4927_; lean_object* v_mctx_4928_; lean_object* v_zetaDeltaFVarIds_4929_; lean_object* v_postponed_4930_; lean_object* v_diag_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4941_; 
v___x_4927_ = lean_st_ref_take(v_a_4923_);
v_mctx_4928_ = lean_ctor_get(v___x_4927_, 0);
v_zetaDeltaFVarIds_4929_ = lean_ctor_get(v___x_4927_, 2);
v_postponed_4930_ = lean_ctor_get(v___x_4927_, 3);
v_diag_4931_ = lean_ctor_get(v___x_4927_, 4);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; 
v_unused_4942_ = lean_ctor_get(v___x_4927_, 1);
lean_dec(v_unused_4942_);
v___x_4933_ = v___x_4927_;
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_diag_4931_);
lean_inc(v_postponed_4930_);
lean_inc(v_zetaDeltaFVarIds_4929_);
lean_inc(v_mctx_4928_);
lean_dec(v___x_4927_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 1, v_cache_4924_);
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_mctx_4928_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_cache_4924_);
lean_ctor_set(v_reuseFailAlloc_4940_, 2, v_zetaDeltaFVarIds_4929_);
lean_ctor_set(v_reuseFailAlloc_4940_, 3, v_postponed_4930_);
lean_ctor_set(v_reuseFailAlloc_4940_, 4, v_diag_4931_);
v___x_4936_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4937_ = lean_st_ref_put(v_a_4923_, v___x_4936_);
v___x_4938_ = lean_box(0);
v___x_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
return v___x_4939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4943_, lean_object* v_cache_4944_, lean_object* v_a_x3f_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4943_, v_cache_4944_, v_a_x3f_4945_);
lean_dec(v_a_x3f_4945_);
lean_dec(v_a_4943_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4948_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; lean_object* v_cache_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4955_ = lean_st_ref_get(v_a_4950_);
v_cache_4956_ = lean_ctor_get(v___x_4955_, 1);
lean_inc_ref(v_cache_4956_);
lean_dec(v___x_4955_);
v___x_4957_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4948_, v___x_4957_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4975_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4961_ = v___x_4958_;
v_isShared_4962_ = v_isSharedCheck_4975_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4975_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
lean_inc(v_a_4959_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set_tag(v___x_4961_, 1);
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
v___x_4965_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4950_, v_cache_4956_, v___x_4964_);
lean_dec_ref(v___x_4964_);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4972_ == 0)
{
lean_object* v_unused_4973_; 
v_unused_4973_ = lean_ctor_get(v___x_4965_, 0);
lean_dec(v_unused_4973_);
v___x_4967_ = v___x_4965_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_dec(v___x_4965_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v_a_4959_);
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4959_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
v_a_4976_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4977_ = lean_box(0);
v___x_4978_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4950_, v_cache_4956_, v___x_4977_);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_4985_ == 0)
{
lean_object* v_unused_4986_; 
v_unused_4986_ = lean_ctor_get(v___x_4978_, 0);
lean_dec(v_unused_4986_);
v___x_4980_ = v___x_4978_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_dec(v___x_4978_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
lean_ctor_set_tag(v___x_4980_, 1);
lean_ctor_set(v___x_4980_, 0, v_a_4976_);
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4976_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
else
{
lean_object* v___x_4987_; 
lean_dec_ref(v_type_4948_);
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4954_);
return v___x_4987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5016_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5016_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5016_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
if (lean_obj_tag(v_a_5002_) == 0)
{
uint8_t v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5006_ = 0;
v___x_5007_ = lean_box(v___x_5006_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v___x_5007_);
v___x_5009_ = v___x_5004_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
else
{
uint8_t v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; 
lean_dec_ref_known(v_a_5002_, 1);
v___x_5011_ = 1;
v___x_5012_ = lean_box(v___x_5011_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v___x_5012_);
v___x_5014_ = v___x_5004_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5012_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v_a_5017_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5001_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5001_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_Meta_isTypeFormerType(v_type_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_);
lean_dec(v_a_5029_);
lean_dec_ref(v_a_5028_);
lean_dec(v_a_5027_);
lean_dec_ref(v_a_5026_);
return v_res_5031_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5032_, lean_object* v_x_5033_){
_start:
{
if (lean_obj_tag(v_x_5032_) == 0)
{
if (lean_obj_tag(v_x_5033_) == 0)
{
uint8_t v___x_5034_; 
v___x_5034_ = 1;
return v___x_5034_;
}
else
{
uint8_t v___x_5035_; 
v___x_5035_ = 0;
return v___x_5035_;
}
}
else
{
if (lean_obj_tag(v_x_5033_) == 0)
{
uint8_t v___x_5036_; 
v___x_5036_ = 0;
return v___x_5036_;
}
else
{
lean_object* v_val_5037_; lean_object* v_val_5038_; uint8_t v___x_5039_; 
v_val_5037_ = lean_ctor_get(v_x_5032_, 0);
v_val_5038_ = lean_ctor_get(v_x_5033_, 0);
v___x_5039_ = lean_level_eq(v_val_5037_, v_val_5038_);
return v___x_5039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5040_, lean_object* v_x_5041_){
_start:
{
uint8_t v_res_5042_; lean_object* v_r_5043_; 
v_res_5042_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5040_, v_x_5041_);
lean_dec(v_x_5041_);
lean_dec(v_x_5040_);
v_r_5043_ = lean_box(v_res_5042_);
return v_r_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5063_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5055_ = v___x_5052_;
v_isShared_5056_ = v_isSharedCheck_5063_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5052_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5063_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5061_; 
v___x_5057_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5058_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5053_, v___x_5057_);
lean_dec(v_a_5053_);
v___x_5059_ = lean_box(v___x_5058_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 0, v___x_5059_);
v___x_5061_ = v___x_5055_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5059_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
v_a_5064_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5052_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5052_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Meta_isPropFormerType(v_type_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5075_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v___x_5085_; 
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
v___x_5085_ = lean_infer_type(v_e_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
v___x_5087_ = l_Lean_Meta_isTypeFormerType(v_a_5086_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
return v___x_5087_;
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
v_a_5088_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5085_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5085_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_Meta_isTypeFormer(v_e_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5097_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5103_, lean_object* v_maxFVars_x3f_5104_, lean_object* v_k_5105_, uint8_t v_cleanupAnnotations_5106_, uint8_t v_whnfType_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v___f_5113_; lean_object* v___x_5114_; 
v___f_5113_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5113_, 0, v_k_5105_);
v___x_5114_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5103_, v_maxFVars_x3f_5104_, v___f_5113_, v_cleanupAnnotations_5106_, v_whnfType_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5114_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5114_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
v_a_5123_ = lean_ctor_get(v___x_5114_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5114_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5114_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5131_, lean_object* v_maxFVars_x3f_5132_, lean_object* v_k_5133_, lean_object* v_cleanupAnnotations_5134_, lean_object* v_whnfType_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5141_; uint8_t v_whnfType_boxed_5142_; lean_object* v_res_5143_; 
v_cleanupAnnotations_boxed_5141_ = lean_unbox(v_cleanupAnnotations_5134_);
v_whnfType_boxed_5142_ = lean_unbox(v_whnfType_5135_);
v_res_5143_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5131_, v_maxFVars_x3f_5132_, v_k_5133_, v_cleanupAnnotations_boxed_5141_, v_whnfType_boxed_5142_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5144_, lean_object* v_type_5145_, lean_object* v_maxFVars_x3f_5146_, lean_object* v_k_5147_, uint8_t v_cleanupAnnotations_5148_, uint8_t v_whnfType_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5145_, v_maxFVars_x3f_5146_, v_k_5147_, v_cleanupAnnotations_5148_, v_whnfType_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5156_, lean_object* v_type_5157_, lean_object* v_maxFVars_x3f_5158_, lean_object* v_k_5159_, lean_object* v_cleanupAnnotations_5160_, lean_object* v_whnfType_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5167_; uint8_t v_whnfType_boxed_5168_; lean_object* v_res_5169_; 
v_cleanupAnnotations_boxed_5167_ = lean_unbox(v_cleanupAnnotations_5160_);
v_whnfType_boxed_5168_ = lean_unbox(v_whnfType_5161_);
v_res_5169_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5156_, v_type_5157_, v_maxFVars_x3f_5158_, v_k_5159_, v_cleanupAnnotations_boxed_5167_, v_whnfType_boxed_5168_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
return v_res_5169_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5170_, lean_object* v_as_5171_, size_t v_i_5172_, size_t v_stop_5173_){
_start:
{
uint8_t v___x_5174_; 
v___x_5174_ = lean_usize_dec_eq(v_i_5172_, v_stop_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; uint8_t v___x_5176_; 
v___x_5175_ = lean_array_uget_borrowed(v_as_5171_, v_i_5172_);
v___x_5176_ = lean_expr_eqv(v_a_5170_, v___x_5175_);
if (v___x_5176_ == 0)
{
size_t v___x_5177_; size_t v___x_5178_; 
v___x_5177_ = ((size_t)1ULL);
v___x_5178_ = lean_usize_add(v_i_5172_, v___x_5177_);
v_i_5172_ = v___x_5178_;
goto _start;
}
else
{
return v___x_5176_;
}
}
else
{
uint8_t v___x_5180_; 
v___x_5180_ = 0;
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5181_, lean_object* v_as_5182_, lean_object* v_i_5183_, lean_object* v_stop_5184_){
_start:
{
size_t v_i_boxed_5185_; size_t v_stop_boxed_5186_; uint8_t v_res_5187_; lean_object* v_r_5188_; 
v_i_boxed_5185_ = lean_unbox_usize(v_i_5183_);
lean_dec(v_i_5183_);
v_stop_boxed_5186_ = lean_unbox_usize(v_stop_5184_);
lean_dec(v_stop_5184_);
v_res_5187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5181_, v_as_5182_, v_i_boxed_5185_, v_stop_boxed_5186_);
lean_dec_ref(v_as_5182_);
lean_dec_ref(v_a_5181_);
v_r_5188_ = lean_box(v_res_5187_);
return v_r_5188_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5191_ = lean_unsigned_to_nat(0u);
v___x_5192_ = lean_array_get_size(v_as_5189_);
v___x_5193_ = lean_nat_dec_lt(v___x_5191_, v___x_5192_);
if (v___x_5193_ == 0)
{
return v___x_5193_;
}
else
{
if (v___x_5193_ == 0)
{
return v___x_5193_;
}
else
{
size_t v___x_5194_; size_t v___x_5195_; uint8_t v___x_5196_; 
v___x_5194_ = ((size_t)0ULL);
v___x_5195_ = lean_usize_of_nat(v___x_5192_);
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5190_, v_as_5189_, v___x_5194_, v___x_5195_);
return v___x_5196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5197_, lean_object* v_a_5198_){
_start:
{
uint8_t v_res_5199_; lean_object* v_r_5200_; 
v_res_5199_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5197_, v_a_5198_);
lean_dec_ref(v_a_5198_);
lean_dec_ref(v_as_5197_);
v_r_5200_ = lean_box(v_res_5199_);
return v_r_5200_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5201_, lean_object* v_e_5202_){
_start:
{
uint8_t v___x_5203_; lean_object* v_d_5205_; lean_object* v_b_5206_; 
v___x_5203_ = l_Lean_Expr_hasFVar(v_e_5202_);
if (v___x_5203_ == 0)
{
lean_dec_ref(v_e_5202_);
return v___x_5203_;
}
else
{
switch(lean_obj_tag(v_e_5202_))
{
case 7:
{
lean_object* v_binderType_5209_; lean_object* v_body_5210_; 
v_binderType_5209_ = lean_ctor_get(v_e_5202_, 1);
lean_inc_ref(v_binderType_5209_);
v_body_5210_ = lean_ctor_get(v_e_5202_, 2);
lean_inc_ref(v_body_5210_);
lean_dec_ref_known(v_e_5202_, 3);
v_d_5205_ = v_binderType_5209_;
v_b_5206_ = v_body_5210_;
goto v___jp_5204_;
}
case 6:
{
lean_object* v_binderType_5211_; lean_object* v_body_5212_; 
v_binderType_5211_ = lean_ctor_get(v_e_5202_, 1);
lean_inc_ref(v_binderType_5211_);
v_body_5212_ = lean_ctor_get(v_e_5202_, 2);
lean_inc_ref(v_body_5212_);
lean_dec_ref_known(v_e_5202_, 3);
v_d_5205_ = v_binderType_5211_;
v_b_5206_ = v_body_5212_;
goto v___jp_5204_;
}
case 10:
{
lean_object* v_expr_5213_; 
v_expr_5213_ = lean_ctor_get(v_e_5202_, 1);
lean_inc_ref(v_expr_5213_);
lean_dec_ref_known(v_e_5202_, 2);
v_e_5202_ = v_expr_5213_;
goto _start;
}
case 8:
{
lean_object* v_type_5215_; lean_object* v_value_5216_; lean_object* v_body_5217_; uint8_t v___x_5218_; 
v_type_5215_ = lean_ctor_get(v_e_5202_, 1);
lean_inc_ref(v_type_5215_);
v_value_5216_ = lean_ctor_get(v_e_5202_, 2);
lean_inc_ref(v_value_5216_);
v_body_5217_ = lean_ctor_get(v_e_5202_, 3);
lean_inc_ref(v_body_5217_);
lean_dec_ref_known(v_e_5202_, 4);
v___x_5218_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5201_, v_type_5215_);
if (v___x_5218_ == 0)
{
uint8_t v___x_5219_; 
v___x_5219_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5201_, v_value_5216_);
if (v___x_5219_ == 0)
{
v_e_5202_ = v_body_5217_;
goto _start;
}
else
{
lean_dec_ref(v_body_5217_);
return v___x_5203_;
}
}
else
{
lean_dec_ref(v_body_5217_);
lean_dec_ref(v_value_5216_);
return v___x_5203_;
}
}
case 5:
{
lean_object* v_fn_5221_; lean_object* v_arg_5222_; uint8_t v___x_5223_; 
v_fn_5221_ = lean_ctor_get(v_e_5202_, 0);
lean_inc_ref(v_fn_5221_);
v_arg_5222_ = lean_ctor_get(v_e_5202_, 1);
lean_inc_ref(v_arg_5222_);
lean_dec_ref_known(v_e_5202_, 2);
v___x_5223_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5201_, v_fn_5221_);
if (v___x_5223_ == 0)
{
v_e_5202_ = v_arg_5222_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5222_);
return v___x_5203_;
}
}
case 11:
{
lean_object* v_struct_5225_; 
v_struct_5225_ = lean_ctor_get(v_e_5202_, 2);
lean_inc_ref(v_struct_5225_);
lean_dec_ref_known(v_e_5202_, 3);
v_e_5202_ = v_struct_5225_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5227_; lean_object* v___x_5228_; uint8_t v___x_5229_; 
v_fvarId_5227_ = lean_ctor_get(v_e_5202_, 0);
lean_inc(v_fvarId_5227_);
lean_dec_ref_known(v_e_5202_, 1);
v___x_5228_ = l_Lean_Expr_fvar___override(v_fvarId_5227_);
v___x_5229_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5201_, v___x_5228_);
lean_dec_ref(v___x_5228_);
return v___x_5229_;
}
default: 
{
uint8_t v___x_5230_; 
lean_dec_ref(v_e_5202_);
v___x_5230_ = 0;
return v___x_5230_;
}
}
}
v___jp_5204_:
{
uint8_t v___x_5207_; 
v___x_5207_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5201_, v_d_5205_);
if (v___x_5207_ == 0)
{
v_e_5202_ = v_b_5206_;
goto _start;
}
else
{
lean_dec_ref(v_b_5206_);
return v___x_5203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5231_, lean_object* v_e_5232_){
_start:
{
uint8_t v_res_5233_; lean_object* v_r_5234_; 
v_res_5233_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5231_, v_e_5232_);
lean_dec_ref(v_xs_5231_);
v_r_5234_ = lean_box(v_res_5233_);
return v_r_5234_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5237_ = l_Lean_stringToMessageData(v___x_5236_);
return v___x_5237_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5240_ = l_Lean_stringToMessageData(v___x_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5241_, lean_object* v_type_5242_, lean_object* v_as_5243_, size_t v_sz_5244_, size_t v_i_5245_, lean_object* v_b_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_a_5253_; uint8_t v___x_5257_; 
v___x_5257_ = lean_usize_dec_lt(v_i_5245_, v_sz_5244_);
if (v___x_5257_ == 0)
{
lean_object* v___x_5258_; 
lean_dec_ref(v_type_5242_);
v___x_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5258_, 0, v_b_5246_);
return v___x_5258_;
}
else
{
lean_object* v___x_5259_; lean_object* v_a_5260_; uint8_t v___x_5261_; 
v___x_5259_ = lean_box(0);
v_a_5260_ = lean_array_uget_borrowed(v_as_5243_, v_i_5245_);
lean_inc(v_a_5260_);
v___x_5261_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5241_, v_a_5260_);
if (v___x_5261_ == 0)
{
v_a_5253_ = v___x_5259_;
goto v___jp_5252_;
}
else
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5260_);
v___x_5263_ = l_Lean_MessageData_ofExpr(v_a_5260_);
v___x_5264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5262_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
v___x_5265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5264_);
lean_ctor_set(v___x_5266_, 1, v___x_5265_);
lean_inc_ref(v_type_5242_);
v___x_5267_ = l_Lean_MessageData_ofExpr(v_type_5242_);
v___x_5268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5266_);
lean_ctor_set(v___x_5268_, 1, v___x_5267_);
v___x_5269_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5268_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_dec_ref_known(v___x_5269_, 1);
v_a_5253_ = v___x_5259_;
goto v___jp_5252_;
}
else
{
lean_dec_ref(v_type_5242_);
return v___x_5269_;
}
}
}
v___jp_5252_:
{
size_t v___x_5254_; size_t v___x_5255_; 
v___x_5254_ = ((size_t)1ULL);
v___x_5255_ = lean_usize_add(v_i_5245_, v___x_5254_);
v_i_5245_ = v___x_5255_;
v_b_5246_ = v_a_5253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5270_, lean_object* v_type_5271_, lean_object* v_as_5272_, lean_object* v_sz_5273_, lean_object* v_i_5274_, lean_object* v_b_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
size_t v_sz_boxed_5281_; size_t v_i_boxed_5282_; lean_object* v_res_5283_; 
v_sz_boxed_5281_ = lean_unbox_usize(v_sz_5273_);
lean_dec(v_sz_5273_);
v_i_boxed_5282_ = lean_unbox_usize(v_i_5274_);
lean_dec(v_i_5274_);
v_res_5283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5270_, v_type_5271_, v_as_5272_, v_sz_boxed_5281_, v_i_boxed_5282_, v_b_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec_ref(v_as_5272_);
lean_dec_ref(v_xs_5270_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5284_, size_t v_i_5285_, lean_object* v_bs_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
uint8_t v___x_5292_; 
v___x_5292_ = lean_usize_dec_lt(v_i_5285_, v_sz_5284_);
if (v___x_5292_ == 0)
{
lean_object* v___x_5293_; 
v___x_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5293_, 0, v_bs_5286_);
return v___x_5293_;
}
else
{
lean_object* v_v_5294_; lean_object* v___x_5295_; 
v_v_5294_ = lean_array_uget_borrowed(v_bs_5286_, v_i_5285_);
lean_inc(v___y_5290_);
lean_inc_ref(v___y_5289_);
lean_inc(v___y_5288_);
lean_inc_ref(v___y_5287_);
lean_inc(v_v_5294_);
v___x_5295_ = lean_infer_type(v_v_5294_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5297_; lean_object* v_bs_x27_5298_; size_t v___x_5299_; size_t v___x_5300_; lean_object* v___x_5301_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5295_, 1);
v___x_5297_ = lean_unsigned_to_nat(0u);
v_bs_x27_5298_ = lean_array_uset(v_bs_5286_, v_i_5285_, v___x_5297_);
v___x_5299_ = ((size_t)1ULL);
v___x_5300_ = lean_usize_add(v_i_5285_, v___x_5299_);
v___x_5301_ = lean_array_uset(v_bs_x27_5298_, v_i_5285_, v_a_5296_);
v_i_5285_ = v___x_5300_;
v_bs_5286_ = v___x_5301_;
goto _start;
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_dec_ref(v_bs_5286_);
v_a_5303_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5295_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5295_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5311_, lean_object* v_i_5312_, lean_object* v_bs_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
size_t v_sz_boxed_5319_; size_t v_i_boxed_5320_; lean_object* v_res_5321_; 
v_sz_boxed_5319_ = lean_unbox_usize(v_sz_5311_);
lean_dec(v_sz_5311_);
v_i_boxed_5320_ = lean_unbox_usize(v_i_5312_);
lean_dec(v_i_5312_);
v_res_5321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5319_, v_i_boxed_5320_, v_bs_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
return v_res_5321_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5323_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5324_ = l_Lean_stringToMessageData(v___x_5323_);
return v___x_5324_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5327_ = l_Lean_stringToMessageData(v___x_5326_);
return v___x_5327_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5329_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5330_ = l_Lean_stringToMessageData(v___x_5329_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5331_, lean_object* v_n_5332_, lean_object* v_xs_5333_, lean_object* v_x_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v___x_5364_; uint8_t v___x_5365_; 
v___x_5364_ = lean_array_get_size(v_xs_5333_);
v___x_5365_ = lean_nat_dec_eq(v___x_5364_, v_n_5332_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec_ref(v_xs_5333_);
v___x_5366_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5367_ = l_Lean_MessageData_ofExpr(v_type_5331_);
v___x_5368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5366_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
v___x_5369_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5368_);
lean_ctor_set(v___x_5370_, 1, v___x_5369_);
v___x_5371_ = l_Nat_reprFast(v_n_5332_);
v___x_5372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5371_);
v___x_5373_ = l_Lean_MessageData_ofFormat(v___x_5372_);
v___x_5374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5370_);
lean_ctor_set(v___x_5374_, 1, v___x_5373_);
v___x_5375_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5376_, 0, v___x_5374_);
lean_ctor_set(v___x_5376_, 1, v___x_5375_);
v___x_5377_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5376_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
v_a_5378_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5377_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5377_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5383_; 
if (v_isShared_5381_ == 0)
{
v___x_5383_ = v___x_5380_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
else
{
lean_dec(v_n_5332_);
goto v___jp_5340_;
}
v___jp_5340_:
{
size_t v_sz_5341_; size_t v___x_5342_; lean_object* v___x_5343_; 
v_sz_5341_ = lean_array_size(v_xs_5333_);
v___x_5342_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5333_);
v___x_5343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5341_, v___x_5342_, v_xs_5333_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5345_; size_t v_sz_5346_; lean_object* v___x_5347_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v___x_5343_, 1);
v___x_5345_ = lean_box(0);
v_sz_5346_ = lean_array_size(v_a_5344_);
v___x_5347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5333_, v_type_5331_, v_a_5344_, v_sz_5346_, v___x_5342_, v___x_5345_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
lean_dec_ref(v_xs_5333_);
if (lean_obj_tag(v___x_5347_) == 0)
{
lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5354_ == 0)
{
lean_object* v_unused_5355_; 
v_unused_5355_ = lean_ctor_get(v___x_5347_, 0);
lean_dec(v_unused_5355_);
v___x_5349_ = v___x_5347_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_dec(v___x_5347_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 0, v_a_5344_);
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5344_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
lean_dec(v_a_5344_);
v_a_5356_ = lean_ctor_get(v___x_5347_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5347_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5347_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5333_);
lean_dec_ref(v_type_5331_);
return v___x_5343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5386_, lean_object* v_n_5387_, lean_object* v_xs_5388_, lean_object* v_x_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5386_, v_n_5387_, v_xs_5388_, v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec_ref(v_x_5389_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5396_, lean_object* v_type_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v___f_5403_; lean_object* v___x_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; 
lean_inc(v_n_5396_);
lean_inc_ref(v_type_5397_);
v___f_5403_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5403_, 0, v_type_5397_);
lean_closure_set(v___f_5403_, 1, v_n_5396_);
v___x_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5404_, 0, v_n_5396_);
v___x_5405_ = 0;
v___x_5406_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5397_, v___x_5404_, v___f_5403_, v___x_5405_, v___x_5405_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5407_, lean_object* v_type_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Lean_Meta_arrowDomainsN(v_n_5407_, v_type_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_);
lean_dec(v_a_5412_);
lean_dec_ref(v_a_5411_);
lean_dec(v_a_5410_);
lean_dec_ref(v_a_5409_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5415_, lean_object* v_e_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v___x_5422_; 
lean_inc(v_a_5420_);
lean_inc_ref(v_a_5419_);
lean_inc(v_a_5418_);
lean_inc_ref(v_a_5417_);
v___x_5422_ = lean_infer_type(v_e_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5424_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref_known(v___x_5422_, 1);
v___x_5424_ = l_Lean_Meta_arrowDomainsN(v_n_5415_, v_a_5423_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_);
return v___x_5424_;
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec(v_n_5415_);
v_a_5425_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5422_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5422_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5433_, lean_object* v_e_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Lean_Meta_inferArgumentTypesN(v_n_5433_, v_e_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
return v_res_5440_;
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
