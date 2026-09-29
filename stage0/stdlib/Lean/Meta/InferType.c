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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* l_instMonadEIO___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object*, lean_object*);
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
lean_dec_ref(v_fn_290_);
lean_dec_ref_known(v_e_285_, 2);
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
v___x_314_ = lean_unsigned_to_nat(1846u);
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
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_780_);
lean_inc(v_fst_794_);
v___x_810_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_794_, v_snd_805_, v_a_780_, v_args_778_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
v___x_811_ = lean_whnf(v___x_810_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
if (lean_obj_tag(v_a_812_) == 7)
{
lean_object* v_body_813_; lean_object* v___x_815_; 
lean_dec(v_snd_805_);
lean_dec(v_fst_794_);
v_body_813_ = lean_ctor_get(v_a_812_, 2);
lean_inc_ref(v_body_813_);
lean_dec_ref_known(v_a_812_, 3);
lean_inc(v_a_780_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_a_780_);
lean_ctor_set(v___x_807_, 0, v_body_813_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_body_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_780_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v_a_788_ = v___x_815_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec(v_a_812_);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_a_780_, v___x_817_);
lean_inc_ref(v_f_779_);
v___x_819_ = l_Lean_mkAppRange(v_f_779_, v___x_809_, v___x_818_, v_args_778_);
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
v_a_832_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_811_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_811_);
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
lean_object* v_toCold_969_; lean_object* v_currRecDepth_970_; lean_object* v_ref_971_; uint16_t v_optionFlags_972_; uint8_t v_suppressElabErrors_973_; uint8_t v_isRecordingDeps_974_; lean_object* v_ref_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_toCold_969_ = lean_ctor_get(v___y_966_, 0);
v_currRecDepth_970_ = lean_ctor_get(v___y_966_, 1);
v_ref_971_ = lean_ctor_get(v___y_966_, 2);
v_optionFlags_972_ = lean_ctor_get_uint16(v___y_966_, sizeof(void*)*3);
v_suppressElabErrors_973_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*3 + 2);
v_isRecordingDeps_974_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*3 + 3);
v_ref_975_ = l_Lean_replaceRef(v_ref_962_, v_ref_971_);
lean_inc(v_currRecDepth_970_);
lean_inc_ref(v_toCold_969_);
v___x_976_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_976_, 0, v_toCold_969_);
lean_ctor_set(v___x_976_, 1, v_currRecDepth_970_);
lean_ctor_set(v___x_976_, 2, v_ref_975_);
lean_ctor_set_uint16(v___x_976_, sizeof(void*)*3, v_optionFlags_972_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*3 + 2, v_suppressElabErrors_973_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*3 + 3, v_isRecordingDeps_974_);
v___x_977_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_963_, v___y_964_, v___y_965_, v___x_976_, v___y_967_);
lean_dec_ref_known(v___x_976_, 3);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_978_, v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v_ref_978_);
return v_res_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
lean_ctor_set(v___x_991_, 3, v___x_990_);
lean_ctor_set(v___x_991_, 4, v___x_989_);
lean_ctor_set(v___x_991_, 5, v___x_989_);
lean_ctor_set(v___x_991_, 6, v___x_989_);
lean_ctor_set(v___x_991_, 7, v___x_989_);
lean_ctor_set(v___x_991_, 8, v___x_989_);
lean_ctor_set(v___x_991_, 9, v___x_989_);
lean_ctor_set(v___x_991_, 10, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_unsigned_to_nat(32u);
v___x_993_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_995_ = ((size_t)5ULL);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_unsigned_to_nat(32u);
v___x_998_ = lean_mk_empty_array_with_capacity(v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1000_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
lean_ctor_set(v___x_1000_, 2, v___x_996_);
lean_ctor_set(v___x_1000_, 3, v___x_996_);
lean_ctor_set_usize(v___x_1000_, 4, v___x_995_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = lean_box(1);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1001_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1026_, lean_object* v_declHint_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_env_1032_; uint8_t v___x_1033_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_st_ref_get(v___y_1028_);
v_env_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_env_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Lean_Name_isAnonymous(v_declHint_1027_);
if (v___x_1033_ == 0)
{
uint8_t v_isExporting_1034_; 
v_isExporting_1034_ = lean_ctor_get_uint8(v_env_1032_, sizeof(void*)*8);
if (v_isExporting_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1027_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_msg_1026_);
return v___x_1035_;
}
else
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
lean_inc_ref(v_env_1032_);
v___x_1036_ = l_Lean_Environment_setExporting(v_env_1032_, v___x_1033_);
lean_inc(v_declHint_1027_);
lean_inc_ref(v___x_1036_);
v___x_1037_ = l_Lean_Environment_contains(v___x_1036_, v_declHint_1027_, v_isExporting_1034_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1027_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_msg_1026_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_c_1044_; lean_object* v___x_1045_; 
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1041_ = l_Lean_Options_empty;
v___x_1042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1039_);
lean_ctor_set(v___x_1042_, 2, v___x_1040_);
lean_ctor_set(v___x_1042_, 3, v___x_1041_);
lean_inc(v_declHint_1027_);
v___x_1043_ = l_Lean_MessageData_ofConstName(v_declHint_1027_, v___x_1033_);
v_c_1044_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1044_, 0, v___x_1042_);
lean_ctor_set(v_c_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1032_, v_declHint_1027_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1027_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_c_1044_);
v___x_1048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_MessageData_note(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_msg_1026_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1087_; 
v_val_1053_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1055_ = v___x_1045_;
v_isShared_1056_ = v_isSharedCheck_1087_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v___x_1045_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1087_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_mod_1059_; uint8_t v___x_1060_; 
v___x_1057_ = l_Lean_Environment_header(v_env_1032_);
lean_dec_ref(v_env_1032_);
v___x_1058_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1057_);
v_mod_1059_ = lean_array_get(v___x_1030_, v___x_1058_, v_val_1053_);
lean_dec(v_val_1053_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l_Lean_isPrivateName(v_declHint_1027_);
lean_dec(v_declHint_1027_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_c_1044_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_ofName(v_mod_1059_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_note(v___x_1068_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_msg_1026_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1070_);
v___x_1072_ = v___x_1055_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_c_1044_);
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Lean_MessageData_ofName(v_mod_1059_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_note(v___x_1081_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_msg_1026_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1083_);
v___x_1085_ = v___x_1055_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1088_; 
lean_dec_ref(v_env_1032_);
lean_dec(v_declHint_1027_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_msg_1026_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1089_, lean_object* v_declHint_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1089_, v_declHint_1090_, v___y_1091_);
lean_dec(v___y_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1094_, lean_object* v_declHint_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1111_; 
v___x_1101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1094_, v_declHint_1095_, v___y_1099_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1106_ = l_Lean_unknownIdentifierMessageTag;
v___x_1107_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1112_, lean_object* v_declHint_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1112_, v_declHint_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1120_, lean_object* v_msg_1121_, lean_object* v_declHint_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_a_1129_; lean_object* v___x_1130_; 
v___x_1128_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1121_, v_declHint_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1120_, v_a_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1131_, lean_object* v_msg_1132_, lean_object* v_declHint_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1131_, v_msg_1132_, v_declHint_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v_ref_1131_);
return v_res_1139_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1146_, lean_object* v_constName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1153_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1154_ = 0;
lean_inc(v_constName_1147_);
v___x_1155_ = l_Lean_MessageData_ofConstName(v_constName_1147_, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1146_, v___x_1158_, v_constName_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1160_, lean_object* v_constName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1160_, v_constName_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_ref_1160_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_ref_1174_; lean_object* v___x_1175_; 
v_ref_1174_ = lean_ctor_get(v___y_1171_, 2);
v___x_1175_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1174_, v_constName_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1189_ = lean_st_ref_get(v___y_1187_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1191_ = 0;
lean_inc(v_constName_1183_);
v___x_1192_ = l_Lean_Environment_findConstVal_x3f(v_env_1190_, v_constName_1183_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1193_;
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_constName_1183_);
v_val_1194_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_val_1194_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_val_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1209_, lean_object* v_us_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; 
lean_inc(v_c_1209_);
v___x_1216_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1209_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v_levelParams_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v_levelParams_1218_ = lean_ctor_get(v_a_1217_, 1);
v___x_1219_ = l_List_lengthTR___redArg(v_levelParams_1218_);
v___x_1220_ = l_List_lengthTR___redArg(v_us_1210_);
v___x_1221_ = lean_nat_dec_eq(v___x_1219_, v___x_1220_);
lean_dec(v___x_1220_);
lean_dec(v___x_1219_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v_a_1217_);
v___x_1222_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1209_, v_us_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_c_1209_);
v___x_1223_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1217_, v_us_1210_, v_a_1214_);
return v___x_1223_;
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_us_1210_);
lean_dec(v_c_1209_);
v_a_1224_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1216_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1216_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1232_, lean_object* v_us_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1232_, v_us_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1240_, lean_object* v_constName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1248_, v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1256_, lean_object* v_ref_1257_, lean_object* v_constName_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1257_, v_constName_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_ref_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1265_, v_ref_1266_, v_constName_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v_ref_1266_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1274_, lean_object* v_ref_1275_, lean_object* v_msg_1276_, lean_object* v_declHint_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1275_, v_msg_1276_, v_declHint_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v_msg_1286_, lean_object* v_declHint_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1284_, v_ref_1285_, v_msg_1286_, v_declHint_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v_ref_1285_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1294_, v_declHint_1295_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1302_, lean_object* v_declHint_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1302_, v_declHint_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1310_, lean_object* v_ref_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1311_, v_msg_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_ref_1320_, lean_object* v_msg_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1319_, v_ref_1320_, v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v_ref_1320_);
return v_res_1327_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1334_, lean_object* v_idx_1335_, lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v_00_u03b1_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1345_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1346_ = l_Lean_mkProj(v_structName_1334_, v_idx_1335_, v_e_1336_);
v___x_1347_ = l_Lean_indentExpr(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1345_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = l_Lean_indentExpr(v_a_1337_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1352_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1354_, lean_object* v_idx_1355_, lean_object* v_e_1356_, lean_object* v_a_1357_, lean_object* v_00_u03b1_1358_, lean_object* v_x_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1354_, v_idx_1355_, v_e_1356_, v_a_1357_, v_00_u03b1_1358_, v_x_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_env_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_st_ref_get(v___y_1370_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_env_1373_);
lean_dec(v___x_1372_);
v___x_1374_ = 0;
lean_inc(v_constName_1366_);
v___x_1375_ = l_Lean_Environment_find_x3f(v_env_1373_, v_constName_1366_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_constName_1366_);
v_val_1377_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_val_1377_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 0);
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_val_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1392_, lean_object* v_structName_1393_, lean_object* v_e_1394_, lean_object* v_idx_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_a_1405_; uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_lt(v_a_1397_, v_upperBound_1392_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_idx_1395_);
lean_dec_ref(v_e_1394_);
lean_dec(v_structName_1393_);
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_b_1398_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; 
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_1411_ = lean_whnf(v_b_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
if (lean_obj_tag(v_a_1412_) == 7)
{
lean_object* v_body_1413_; uint8_t v___x_1414_; 
v_body_1413_ = lean_ctor_get(v_a_1412_, 2);
lean_inc_ref(v_body_1413_);
lean_dec_ref_known(v_a_1412_, 3);
v___x_1414_ = l_Lean_Expr_hasLooseBVars(v_body_1413_);
if (v___x_1414_ == 0)
{
v_a_1405_ = v_body_1413_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_inc_ref(v_e_1394_);
lean_inc(v_a_1397_);
lean_inc(v_structName_1393_);
v___x_1415_ = l_Lean_mkProj(v_structName_1393_, v_a_1397_, v_e_1394_);
v___x_1416_ = lean_expr_instantiate1(v_body_1413_, v___x_1415_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v_body_1413_);
v_a_1405_ = v___x_1416_;
goto v___jp_1404_;
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1394_);
lean_inc(v_idx_1395_);
lean_inc(v_structName_1393_);
v___x_1418_ = l_Lean_mkProj(v_structName_1393_, v_idx_1395_, v_e_1394_);
v___x_1419_ = l_Lean_indentExpr(v___x_1418_);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1417_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
lean_inc_ref(v_a_1396_);
v___x_1423_ = l_Lean_indentExpr(v_a_1396_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1424_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_dec_ref_known(v___x_1425_, 1);
v_a_1405_ = v_a_1412_;
goto v___jp_1404_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_a_1412_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_idx_1395_);
lean_dec_ref(v_e_1394_);
lean_dec(v_structName_1393_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_idx_1395_);
lean_dec_ref(v_e_1394_);
lean_dec(v_structName_1393_);
return v___x_1411_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_add(v_a_1397_, v___x_1406_);
lean_dec(v_a_1397_);
v_a_1397_ = v___x_1407_;
v_b_1398_ = v_a_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1434_, lean_object* v_structName_1435_, lean_object* v_e_1436_, lean_object* v_idx_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1434_, v_structName_1435_, v_e_1436_, v_idx_1437_, v_a_1438_, v_a_1439_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v_upperBound_1434_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1447_, lean_object* v_structName_1448_, lean_object* v_e_1449_, lean_object* v_idx_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_a_1460_; uint8_t v___x_1464_; 
v___x_1464_ = lean_nat_dec_lt(v_a_1452_, v_upperBound_1447_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_idx_1450_);
lean_dec_ref(v_e_1449_);
lean_dec(v_structName_1448_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1453_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; 
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
v___x_1466_ = lean_whnf(v_b_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
if (lean_obj_tag(v_a_1467_) == 7)
{
lean_object* v_body_1468_; uint8_t v___x_1469_; 
v_body_1468_ = lean_ctor_get(v_a_1467_, 2);
lean_inc_ref(v_body_1468_);
lean_dec_ref_known(v_a_1467_, 3);
v___x_1469_ = l_Lean_Expr_hasLooseBVars(v_body_1468_);
if (v___x_1469_ == 0)
{
v_a_1460_ = v_body_1468_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_inc_ref(v_e_1449_);
lean_inc(v_a_1452_);
lean_inc(v_structName_1448_);
v___x_1470_ = l_Lean_mkProj(v_structName_1448_, v_a_1452_, v_e_1449_);
v___x_1471_ = lean_expr_instantiate1(v_body_1468_, v___x_1470_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_body_1468_);
v_a_1460_ = v___x_1471_;
goto v___jp_1459_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1449_);
lean_inc(v_idx_1450_);
lean_inc(v_structName_1448_);
v___x_1473_ = l_Lean_mkProj(v_structName_1448_, v_idx_1450_, v_e_1449_);
v___x_1474_ = l_Lean_indentExpr(v___x_1473_);
v___x_1475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
lean_inc_ref(v_a_1451_);
v___x_1478_ = l_Lean_indentExpr(v_a_1451_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1479_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref_known(v___x_1480_, 1);
v_a_1460_ = v_a_1467_;
goto v___jp_1459_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1467_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_idx_1450_);
lean_dec_ref(v_e_1449_);
lean_dec(v_structName_1448_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
else
{
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_idx_1450_);
lean_dec_ref(v_e_1449_);
lean_dec(v_structName_1448_);
return v___x_1466_;
}
}
v___jp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_a_1452_, v___x_1461_);
lean_dec(v_a_1452_);
v___x_1463_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1447_, v_structName_1448_, v_e_1449_, v_idx_1450_, v_a_1451_, v___x_1462_, v_a_1460_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1489_, lean_object* v_structName_1490_, lean_object* v_e_1491_, lean_object* v_idx_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1489_, v_structName_1490_, v_e_1491_, v_idx_1492_, v_a_1493_, v_a_1494_, v_b_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_upperBound_1489_);
return v_res_1501_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1502_; lean_object* v_dummy_1503_; 
v___x_1502_ = lean_box(0);
v_dummy_1503_ = l_Lean_Expr_sort___override(v___x_1502_);
return v_dummy_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1504_, lean_object* v_idx_1505_, lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1512_; 
lean_inc(v_a_1510_);
lean_inc_ref(v_a_1509_);
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc_ref(v_e_1506_);
v___x_1512_ = lean_infer_type(v_e_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
lean_inc(v_a_1510_);
lean_inc_ref(v_a_1509_);
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
v___x_1514_ = lean_whnf(v_a_1513_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = l_Lean_Expr_getAppFn(v_a_1515_);
if (lean_obj_tag(v___x_1516_) == 4)
{
lean_object* v_declName_1517_; lean_object* v_us_1518_; lean_object* v___x_1519_; lean_object* v_env_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v_declName_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_declName_1517_);
v_us_1518_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_us_1518_);
lean_dec_ref_known(v___x_1516_, 2);
v___x_1519_ = lean_st_ref_get(v_a_1510_);
v_env_1523_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_ref(v_env_1523_);
lean_dec(v___x_1519_);
v___x_1524_ = 0;
v___x_1525_ = l_Lean_Environment_find_x3f(v_env_1523_, v_declName_1517_, v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_us_1518_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1526_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; 
v_val_1528_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_val_1528_);
lean_dec_ref_known(v___x_1525_, 1);
if (lean_obj_tag(v_val_1528_) == 5)
{
lean_object* v_val_1529_; lean_object* v_ctors_1530_; 
v_val_1529_ = lean_ctor_get(v_val_1528_, 0);
lean_inc_ref(v_val_1529_);
lean_dec_ref_known(v_val_1528_, 1);
v_ctors_1530_ = lean_ctor_get(v_val_1529_, 4);
lean_inc(v_ctors_1530_);
if (lean_obj_tag(v_ctors_1530_) == 1)
{
lean_object* v_tail_1531_; 
v_tail_1531_ = lean_ctor_get(v_ctors_1530_, 1);
if (lean_obj_tag(v_tail_1531_) == 0)
{
lean_object* v_toConstantVal_1532_; lean_object* v_numParams_1533_; lean_object* v_numIndices_1534_; lean_object* v_head_1535_; lean_object* v___x_1536_; 
v_toConstantVal_1532_ = lean_ctor_get(v_val_1529_, 0);
lean_inc_ref(v_toConstantVal_1532_);
v_numParams_1533_ = lean_ctor_get(v_val_1529_, 1);
lean_inc(v_numParams_1533_);
v_numIndices_1534_ = lean_ctor_get(v_val_1529_, 2);
lean_inc(v_numIndices_1534_);
lean_dec_ref(v_val_1529_);
v_head_1535_ = lean_ctor_get(v_ctors_1530_, 0);
lean_inc(v_head_1535_);
lean_dec_ref_known(v_ctors_1530_, 2);
v___x_1536_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1535_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (lean_obj_tag(v_a_1537_) == 6)
{
lean_object* v_val_1538_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v_name_1578_; uint8_t v___x_1579_; 
v_val_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc_ref(v_val_1538_);
lean_dec_ref_known(v_a_1537_, 1);
v_name_1578_ = lean_ctor_get(v_toConstantVal_1532_, 0);
lean_inc(v_name_1578_);
lean_dec_ref(v_toConstantVal_1532_);
v___x_1579_ = lean_name_eq(v_name_1578_, v_structName_1504_);
lean_dec(v_name_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_val_1538_);
lean_dec(v_numIndices_1534_);
lean_dec(v_numParams_1533_);
lean_dec(v_us_1518_);
v___x_1580_ = lean_box(0);
v___x_1581_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1580_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
else
{
v___y_1540_ = v_a_1507_;
v___y_1541_ = v_a_1508_;
v___y_1542_ = v_a_1509_;
v___y_1543_ = v_a_1510_;
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v_dummy_1544_; lean_object* v_nargs_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_dummy_1544_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1545_ = l_Lean_Expr_getAppNumArgs(v_a_1515_);
lean_inc(v_nargs_1545_);
v___x_1546_ = lean_mk_array(v_nargs_1545_, v_dummy_1544_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_sub(v_nargs_1545_, v___x_1547_);
lean_dec(v_nargs_1545_);
lean_inc(v_a_1515_);
v___x_1549_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1515_, v___x_1546_, v___x_1548_);
v___x_1550_ = lean_nat_add(v_numParams_1533_, v_numIndices_1534_);
lean_dec(v_numIndices_1534_);
v___x_1551_ = lean_array_get_size(v___x_1549_);
v___x_1552_ = lean_nat_dec_eq(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref(v___x_1549_);
lean_dec_ref(v_val_1538_);
lean_dec(v_numParams_1533_);
lean_dec(v_us_1518_);
v___x_1553_ = lean_box(0);
v___x_1554_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1553_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1554_;
}
else
{
lean_object* v_toConstantVal_1555_; lean_object* v_name_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_toConstantVal_1555_ = lean_ctor_get(v_val_1538_, 0);
lean_inc_ref(v_toConstantVal_1555_);
lean_dec_ref(v_val_1538_);
v_name_1556_ = lean_ctor_get(v_toConstantVal_1555_, 0);
lean_inc(v_name_1556_);
lean_dec_ref(v_toConstantVal_1555_);
v___x_1557_ = l_Lean_mkConst(v_name_1556_, v_us_1518_);
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = l_Array_toSubarray___redArg(v___x_1549_, v___x_1558_, v_numParams_1533_);
v___x_1560_ = l_Subarray_copy___redArg(v___x_1559_);
v___x_1561_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1557_, v___x_1560_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc(v_a_1515_);
lean_inc_ref(v_e_1506_);
lean_inc(v_structName_1504_);
lean_inc(v_idx_1505_);
v___x_1563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1505_, v_structName_1504_, v_e_1506_, v_idx_1505_, v_a_1515_, v___x_1558_, v_a_1562_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
v___x_1565_ = lean_whnf(v_a_1564_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1577_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1577_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1577_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
if (lean_obj_tag(v_a_1566_) == 7)
{
lean_object* v_binderType_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec(v_a_1515_);
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
v_binderType_1570_ = lean_ctor_get(v_a_1566_, 1);
lean_inc_ref(v_binderType_1570_);
lean_dec_ref_known(v_a_1566_, 3);
v___x_1571_ = lean_expr_consume_type_annotations(v_binderType_1570_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_del_object(v___x_1568_);
lean_dec(v_a_1566_);
v___x_1575_ = lean_box(0);
v___x_1576_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1575_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1576_;
}
}
}
else
{
lean_dec(v_a_1515_);
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
return v___x_1565_;
}
}
else
{
lean_dec(v_a_1515_);
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
return v___x_1563_;
}
}
else
{
lean_dec(v_a_1515_);
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
return v___x_1561_;
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v_a_1537_);
lean_dec(v_numIndices_1534_);
lean_dec(v_numParams_1533_);
lean_dec_ref(v_toConstantVal_1532_);
lean_dec(v_us_1518_);
v___x_1590_ = lean_box(0);
v___x_1591_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1590_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1591_;
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_numIndices_1534_);
lean_dec(v_numParams_1533_);
lean_dec_ref(v_toConstantVal_1532_);
lean_dec(v_us_1518_);
lean_dec(v_a_1515_);
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
v_a_1592_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1536_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1536_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1530_, 2);
lean_dec_ref(v_val_1529_);
lean_dec(v_us_1518_);
goto v___jp_1520_;
}
}
else
{
lean_dec(v_ctors_1530_);
lean_dec_ref(v_val_1529_);
lean_dec(v_us_1518_);
goto v___jp_1520_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_val_1528_);
lean_dec(v_us_1518_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1600_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1601_;
}
}
v___jp_1520_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1521_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1522_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v___x_1516_);
v___x_1602_ = lean_box(0);
v___x_1603_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1504_, v_idx_1505_, v_e_1506_, v_a_1515_, lean_box(0), v___x_1602_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1603_;
}
}
else
{
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
return v___x_1514_;
}
}
else
{
lean_dec_ref(v_e_1506_);
lean_dec(v_idx_1505_);
lean_dec(v_structName_1504_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1604_, lean_object* v_idx_1605_, lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1604_, v_idx_1605_, v_e_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1613_, lean_object* v_structName_1614_, lean_object* v_e_1615_, lean_object* v_idx_1616_, lean_object* v_a_1617_, lean_object* v_inst_1618_, lean_object* v_R_1619_, lean_object* v_a_1620_, lean_object* v_b_1621_, lean_object* v_c_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1613_, v_structName_1614_, v_e_1615_, v_idx_1616_, v_a_1617_, v_a_1620_, v_b_1621_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1629_, lean_object* v_structName_1630_, lean_object* v_e_1631_, lean_object* v_idx_1632_, lean_object* v_a_1633_, lean_object* v_inst_1634_, lean_object* v_R_1635_, lean_object* v_a_1636_, lean_object* v_b_1637_, lean_object* v_c_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1629_, v_structName_1630_, v_e_1631_, v_idx_1632_, v_a_1633_, v_inst_1634_, v_R_1635_, v_a_1636_, v_b_1637_, v_c_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v_upperBound_1629_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1645_, lean_object* v_structName_1646_, lean_object* v_e_1647_, lean_object* v_idx_1648_, lean_object* v_a_1649_, lean_object* v_inst_1650_, lean_object* v_R_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_c_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1645_, v_structName_1646_, v_e_1647_, v_idx_1648_, v_a_1649_, v_a_1652_, v_b_1653_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1661_, lean_object* v_structName_1662_, lean_object* v_e_1663_, lean_object* v_idx_1664_, lean_object* v_a_1665_, lean_object* v_inst_1666_, lean_object* v_R_1667_, lean_object* v_a_1668_, lean_object* v_b_1669_, lean_object* v_c_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1661_, v_structName_1662_, v_e_1663_, v_idx_1664_, v_a_1665_, v_inst_1666_, v_R_1667_, v_a_1668_, v_b_1669_, v_c_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v_upperBound_1661_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1686_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1687_ = l_Lean_indentExpr(v_type_1680_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1688_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1697_, lean_object* v_type_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_type_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1705_, v_type_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v_ks_1717_; lean_object* v_vs_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1742_; 
v_ks_1717_ = lean_ctor_get(v_x_1713_, 0);
v_vs_1718_ = lean_ctor_get(v_x_1713_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_x_1713_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1720_ = v_x_1713_;
v_isShared_1721_ = v_isSharedCheck_1742_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_vs_1718_);
lean_inc(v_ks_1717_);
lean_dec(v_x_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1742_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = lean_array_get_size(v_ks_1717_);
v___x_1723_ = lean_nat_dec_lt(v_x_1714_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec(v_x_1714_);
v___x_1724_ = lean_array_push(v_ks_1717_, v_x_1715_);
v___x_1725_ = lean_array_push(v_vs_1718_, v_x_1716_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1725_);
lean_ctor_set(v___x_1720_, 0, v___x_1724_);
v___x_1727_ = v___x_1720_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
else
{
lean_object* v_k_x27_1729_; uint8_t v___x_1730_; 
v_k_x27_1729_ = lean_array_fget_borrowed(v_ks_1717_, v_x_1714_);
v___x_1730_ = l_Lean_instBEqMVarId_beq(v_x_1715_, v_k_x27_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1732_; 
if (v_isShared_1721_ == 0)
{
v___x_1732_ = v___x_1720_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_ks_1717_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_vs_1718_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_x_1714_, v___x_1733_);
lean_dec(v_x_1714_);
v_x_1713_ = v___x_1732_;
v_x_1714_ = v___x_1734_;
goto _start;
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1737_ = lean_array_fset(v_ks_1717_, v_x_1714_, v_x_1715_);
v___x_1738_ = lean_array_fset(v_vs_1718_, v_x_1714_, v_x_1716_);
lean_dec(v_x_1714_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1738_);
lean_ctor_set(v___x_1720_, 0, v___x_1737_);
v___x_1740_ = v___x_1720_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1743_, lean_object* v_k_1744_, lean_object* v_v_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1743_, v___x_1746_, v_k_1744_, v_v_1745_);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1749_, size_t v_x_1750_, size_t v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1749_) == 0)
{
lean_object* v_es_1754_; size_t v___x_1755_; size_t v___x_1756_; lean_object* v_j_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_es_1754_ = lean_ctor_get(v_x_1749_, 0);
v___x_1755_ = ((size_t)31ULL);
v___x_1756_ = lean_usize_land(v_x_1750_, v___x_1755_);
v_j_1757_ = lean_usize_to_nat(v___x_1756_);
v___x_1758_ = lean_array_get_size(v_es_1754_);
v___x_1759_ = lean_nat_dec_lt(v_j_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_dec(v_j_1757_);
lean_dec(v_x_1753_);
lean_dec(v_x_1752_);
return v_x_1749_;
}
else
{
lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1798_; 
lean_inc_ref(v_es_1754_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_x_1749_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_x_1749_, 0);
lean_dec(v_unused_1799_);
v___x_1761_ = v_x_1749_;
v_isShared_1762_ = v_isSharedCheck_1798_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v_x_1749_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1798_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_v_1763_; lean_object* v___x_1764_; lean_object* v_xs_x27_1765_; lean_object* v___y_1767_; 
v_v_1763_ = lean_array_fget(v_es_1754_, v_j_1757_);
v___x_1764_ = lean_box(0);
v_xs_x27_1765_ = lean_array_fset(v_es_1754_, v_j_1757_, v___x_1764_);
switch(lean_obj_tag(v_v_1763_))
{
case 0:
{
lean_object* v_key_1772_; lean_object* v_val_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
v_key_1772_ = lean_ctor_get(v_v_1763_, 0);
v_val_1773_ = lean_ctor_get(v_v_1763_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_v_1763_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1775_ = v_v_1763_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_val_1773_);
lean_inc(v_key_1772_);
lean_dec(v_v_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
uint8_t v___x_1777_; 
v___x_1777_ = l_Lean_instBEqMVarId_beq(v_x_1752_, v_key_1772_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_del_object(v___x_1775_);
v___x_1778_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1772_, v_val_1773_, v_x_1752_, v_x_1753_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
v___y_1767_ = v___x_1779_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1781_; 
lean_dec(v_val_1773_);
lean_dec(v_key_1772_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v_x_1753_);
lean_ctor_set(v___x_1775_, 0, v_x_1752_);
v___x_1781_ = v___x_1775_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_x_1752_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_x_1753_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v___y_1767_ = v___x_1781_;
goto v___jp_1766_;
}
}
}
}
case 1:
{
lean_object* v_node_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1796_; 
v_node_1784_ = lean_ctor_get(v_v_1763_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_v_1763_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1786_ = v_v_1763_;
v_isShared_1787_ = v_isSharedCheck_1796_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_node_1784_);
lean_dec(v_v_1763_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1796_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
size_t v___x_1788_; size_t v___x_1789_; size_t v___x_1790_; size_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1788_ = ((size_t)5ULL);
v___x_1789_ = lean_usize_shift_right(v_x_1750_, v___x_1788_);
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_x_1751_, v___x_1790_);
v___x_1792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1784_, v___x_1789_, v___x_1791_, v_x_1752_, v_x_1753_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1792_);
v___x_1794_ = v___x_1786_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v___y_1767_ = v___x_1794_;
goto v___jp_1766_;
}
}
}
default: 
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_x_1752_);
lean_ctor_set(v___x_1797_, 1, v_x_1753_);
v___y_1767_ = v___x_1797_;
goto v___jp_1766_;
}
}
v___jp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_array_fset(v_xs_x27_1765_, v_j_1757_, v___y_1767_);
lean_dec(v_j_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1768_);
v___x_1770_ = v___x_1761_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v_ks_1800_; lean_object* v_vs_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1819_; 
v_ks_1800_ = lean_ctor_get(v_x_1749_, 0);
v_vs_1801_ = lean_ctor_get(v_x_1749_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1749_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1803_ = v_x_1749_;
v_isShared_1804_ = v_isSharedCheck_1819_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_vs_1801_);
lean_inc(v_ks_1800_);
lean_dec(v_x_1749_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1819_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_ks_1800_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_vs_1801_);
v___x_1806_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v_newNode_1807_; size_t v___x_1808_; uint8_t v___x_1809_; 
v_newNode_1807_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1806_, v_x_1752_, v_x_1753_);
v___x_1808_ = ((size_t)7ULL);
v___x_1809_ = lean_usize_dec_le(v___x_1808_, v_x_1751_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1807_);
v___x_1811_ = lean_unsigned_to_nat(4u);
v___x_1812_ = lean_nat_dec_lt(v___x_1810_, v___x_1811_);
lean_dec(v___x_1810_);
if (v___x_1812_ == 0)
{
lean_object* v_ks_1813_; lean_object* v_vs_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_ks_1813_ = lean_ctor_get(v_newNode_1807_, 0);
lean_inc_ref(v_ks_1813_);
v_vs_1814_ = lean_ctor_get(v_newNode_1807_, 1);
lean_inc_ref(v_vs_1814_);
lean_dec_ref(v_newNode_1807_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1751_, v_ks_1813_, v_vs_1814_, v___x_1815_, v___x_1816_);
lean_dec_ref(v_vs_1814_);
lean_dec_ref(v_ks_1813_);
return v___x_1817_;
}
else
{
return v_newNode_1807_;
}
}
else
{
return v_newNode_1807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1820_, lean_object* v_keys_1821_, lean_object* v_vals_1822_, lean_object* v_i_1823_, lean_object* v_entries_1824_){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_keys_1821_);
v___x_1826_ = lean_nat_dec_lt(v_i_1823_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_dec(v_i_1823_);
return v_entries_1824_;
}
else
{
lean_object* v_k_1827_; lean_object* v_v_1828_; uint64_t v___x_1829_; size_t v_h_1830_; size_t v___x_1831_; lean_object* v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; size_t v_h_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_k_1827_ = lean_array_fget_borrowed(v_keys_1821_, v_i_1823_);
v_v_1828_ = lean_array_fget_borrowed(v_vals_1822_, v_i_1823_);
v___x_1829_ = l_Lean_instHashableMVarId_hash(v_k_1827_);
v_h_1830_ = lean_uint64_to_usize(v___x_1829_);
v___x_1831_ = ((size_t)5ULL);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_sub(v_depth_1820_, v___x_1833_);
v___x_1835_ = lean_usize_mul(v___x_1831_, v___x_1834_);
v_h_1836_ = lean_usize_shift_right(v_h_1830_, v___x_1835_);
v___x_1837_ = lean_nat_add(v_i_1823_, v___x_1832_);
lean_dec(v_i_1823_);
lean_inc(v_v_1828_);
lean_inc(v_k_1827_);
v___x_1838_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1824_, v_h_1836_, v_depth_1820_, v_k_1827_, v_v_1828_);
v_i_1823_ = v___x_1837_;
v_entries_1824_ = v___x_1838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1840_, lean_object* v_keys_1841_, lean_object* v_vals_1842_, lean_object* v_i_1843_, lean_object* v_entries_1844_){
_start:
{
size_t v_depth_boxed_1845_; lean_object* v_res_1846_; 
v_depth_boxed_1845_ = lean_unbox_usize(v_depth_1840_);
lean_dec(v_depth_1840_);
v_res_1846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1845_, v_keys_1841_, v_vals_1842_, v_i_1843_, v_entries_1844_);
lean_dec_ref(v_vals_1842_);
lean_dec_ref(v_keys_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
size_t v_x_1151__boxed_1852_; size_t v_x_1152__boxed_1853_; lean_object* v_res_1854_; 
v_x_1151__boxed_1852_ = lean_unbox_usize(v_x_1848_);
lean_dec(v_x_1848_);
v_x_1152__boxed_1853_ = lean_unbox_usize(v_x_1849_);
lean_dec(v_x_1849_);
v_res_1854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1847_, v_x_1151__boxed_1852_, v_x_1152__boxed_1853_, v_x_1850_, v_x_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
uint64_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = l_Lean_instHashableMVarId_hash(v_x_1856_);
v___x_1859_ = lean_uint64_to_usize(v___x_1858_);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1855_, v___x_1859_, v___x_1860_, v_x_1856_, v_x_1857_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1862_, lean_object* v_val_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_mctx_1867_; lean_object* v_cache_1868_; lean_object* v_zetaDeltaFVarIds_1869_; lean_object* v_postponed_1870_; lean_object* v_diag_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1900_; 
v___x_1866_ = lean_st_ref_take(v___y_1864_);
v_mctx_1867_ = lean_ctor_get(v___x_1866_, 0);
v_cache_1868_ = lean_ctor_get(v___x_1866_, 1);
v_zetaDeltaFVarIds_1869_ = lean_ctor_get(v___x_1866_, 2);
v_postponed_1870_ = lean_ctor_get(v___x_1866_, 3);
v_diag_1871_ = lean_ctor_get(v___x_1866_, 4);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1873_ = v___x_1866_;
v_isShared_1874_ = v_isSharedCheck_1900_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_diag_1871_);
lean_inc(v_postponed_1870_);
lean_inc(v_zetaDeltaFVarIds_1869_);
lean_inc(v_cache_1868_);
lean_inc(v_mctx_1867_);
lean_dec(v___x_1866_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1900_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_depth_1875_; lean_object* v_levelAssignDepth_1876_; lean_object* v_lmvarCounter_1877_; lean_object* v_mvarCounter_1878_; lean_object* v_lDecls_1879_; lean_object* v_decls_1880_; lean_object* v_userNames_1881_; lean_object* v_lAssignment_1882_; lean_object* v_eAssignment_1883_; lean_object* v_dAssignment_1884_; lean_object* v_instanceTypedMVars_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1899_; 
v_depth_1875_ = lean_ctor_get(v_mctx_1867_, 0);
v_levelAssignDepth_1876_ = lean_ctor_get(v_mctx_1867_, 1);
v_lmvarCounter_1877_ = lean_ctor_get(v_mctx_1867_, 2);
v_mvarCounter_1878_ = lean_ctor_get(v_mctx_1867_, 3);
v_lDecls_1879_ = lean_ctor_get(v_mctx_1867_, 4);
v_decls_1880_ = lean_ctor_get(v_mctx_1867_, 5);
v_userNames_1881_ = lean_ctor_get(v_mctx_1867_, 6);
v_lAssignment_1882_ = lean_ctor_get(v_mctx_1867_, 7);
v_eAssignment_1883_ = lean_ctor_get(v_mctx_1867_, 8);
v_dAssignment_1884_ = lean_ctor_get(v_mctx_1867_, 9);
v_instanceTypedMVars_1885_ = lean_ctor_get(v_mctx_1867_, 10);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_mctx_1867_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1887_ = v_mctx_1867_;
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_instanceTypedMVars_1885_);
lean_inc(v_dAssignment_1884_);
lean_inc(v_eAssignment_1883_);
lean_inc(v_lAssignment_1882_);
lean_inc(v_userNames_1881_);
lean_inc(v_decls_1880_);
lean_inc(v_lDecls_1879_);
lean_inc(v_mvarCounter_1878_);
lean_inc(v_lmvarCounter_1877_);
lean_inc(v_levelAssignDepth_1876_);
lean_inc(v_depth_1875_);
lean_dec(v_mctx_1867_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1883_, v_mvarId_1862_, v_val_1863_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 8, v___x_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_depth_1875_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_levelAssignDepth_1876_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_lmvarCounter_1877_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_mvarCounter_1878_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_lDecls_1879_);
lean_ctor_set(v_reuseFailAlloc_1898_, 5, v_decls_1880_);
lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_userNames_1881_);
lean_ctor_set(v_reuseFailAlloc_1898_, 7, v_lAssignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1898_, 8, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 9, v_dAssignment_1884_);
lean_ctor_set(v_reuseFailAlloc_1898_, 10, v_instanceTypedMVars_1885_);
v___x_1892_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1892_);
v___x_1894_ = v___x_1873_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_zetaDeltaFVarIds_1869_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_postponed_1870_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_diag_1871_);
v___x_1894_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_st_ref_put(v___y_1864_, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1889_);
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1901_, lean_object* v_val_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1901_, v_val_1902_, v___y_1903_);
lean_dec(v___y_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; 
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc_ref(v_type_1906_);
v___x_1912_ = lean_infer_type(v_type_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = l_Lean_Meta_whnfD(v_a_1913_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1949_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1949_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1949_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
switch(lean_obj_tag(v_a_1915_))
{
case 3:
{
lean_object* v_u_1919_; lean_object* v___x_1921_; 
lean_dec_ref(v_type_1906_);
v_u_1919_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_u_1919_);
lean_dec_ref_known(v_a_1915_, 1);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v_u_1919_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_u_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
case 2:
{
lean_object* v_mvarId_1923_; lean_object* v___x_1924_; 
lean_del_object(v___x_1917_);
v_mvarId_1923_ = lean_ctor_get(v_a_1915_, 0);
lean_inc_n(v_mvarId_1923_, 2);
lean_dec_ref_known(v_a_1915_, 1);
v___x_1924_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1923_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; uint8_t v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v_type_1906_);
v___x_1927_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_n(v_a_1928_, 2);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l_Lean_mkSort(v_a_1928_);
v___x_1930_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1923_, v___x_1929_, v_a_1908_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1930_, 0);
lean_dec(v_unused_1938_);
v___x_1932_ = v___x_1930_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_dec(v___x_1930_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1928_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1928_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_dec(v_mvarId_1923_);
return v___x_1927_;
}
}
else
{
lean_object* v___x_1939_; 
lean_dec(v_mvarId_1923_);
v___x_1939_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1939_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_mvarId_1923_);
lean_dec_ref(v_type_1906_);
v_a_1940_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1924_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1924_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
default: 
{
lean_object* v___x_1948_; 
lean_del_object(v___x_1917_);
lean_dec(v_a_1915_);
v___x_1948_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_type_1906_);
v_a_1950_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1914_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1914_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_type_1906_);
v_a_1958_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1912_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1912_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_getLevel(v_type_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1973_, lean_object* v_val_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1973_, v_val_1974_, v___y_1976_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1981_, lean_object* v_val_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1981_, v_val_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1990_, v_x_1991_, v_x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1994_, lean_object* v_x_1995_, size_t v_x_1996_, size_t v_x_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1995_, v_x_1996_, v_x_1997_, v_x_1998_, v_x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
size_t v_x_1500__boxed_2007_; size_t v_x_1501__boxed_2008_; lean_object* v_res_2009_; 
v_x_1500__boxed_2007_ = lean_unbox_usize(v_x_2003_);
lean_dec(v_x_2003_);
v_x_1501__boxed_2008_ = lean_unbox_usize(v_x_2004_);
lean_dec(v_x_2004_);
v_res_2009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2001_, v_x_2002_, v_x_1500__boxed_2007_, v_x_1501__boxed_2008_, v_x_2005_, v_x_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2010_, lean_object* v_n_2011_, lean_object* v_k_2012_, lean_object* v_v_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2011_, v_k_2012_, v_v_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2015_, size_t v_depth_2016_, lean_object* v_keys_2017_, lean_object* v_vals_2018_, lean_object* v_heq_2019_, lean_object* v_i_2020_, lean_object* v_entries_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2016_, v_keys_2017_, v_vals_2018_, v_i_2020_, v_entries_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2023_, lean_object* v_depth_2024_, lean_object* v_keys_2025_, lean_object* v_vals_2026_, lean_object* v_heq_2027_, lean_object* v_i_2028_, lean_object* v_entries_2029_){
_start:
{
size_t v_depth_boxed_2030_; lean_object* v_res_2031_; 
v_depth_boxed_2030_ = lean_unbox_usize(v_depth_2024_);
lean_dec(v_depth_2024_);
v_res_2031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2023_, v_depth_boxed_2030_, v_keys_2025_, v_vals_2026_, v_heq_2027_, v_i_2028_, v_entries_2029_);
lean_dec_ref(v_vals_2026_);
lean_dec_ref(v_keys_2025_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2033_, v_x_2034_, v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2038_, lean_object* v_b_2039_, lean_object* v_c_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
v___x_2046_ = lean_apply_7(v_k_2038_, v_b_2039_, v_c_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2047_, lean_object* v_b_2048_, lean_object* v_c_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2047_, v_b_2048_, v_c_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2056_, lean_object* v_k_2057_, uint8_t v_cleanupAnnotations_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___f_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2064_, 0, v_k_2057_);
v___x_2065_ = 0;
v___x_2066_ = lean_box(0);
v___x_2067_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2065_, v___x_2066_, v_type_2056_, v___f_2064_, v_cleanupAnnotations_2058_, v___x_2065_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2067_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2067_);
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
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2084_, lean_object* v_k_2085_, lean_object* v_cleanupAnnotations_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2092_; lean_object* v_res_2093_; 
v_cleanupAnnotations_boxed_2092_ = lean_unbox(v_cleanupAnnotations_2086_);
v_res_2093_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2084_, v_k_2085_, v_cleanupAnnotations_boxed_2092_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2094_, lean_object* v_type_2095_, lean_object* v_k_2096_, uint8_t v_cleanupAnnotations_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2095_, v_k_2096_, v_cleanupAnnotations_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_type_2105_, lean_object* v_k_2106_, lean_object* v_cleanupAnnotations_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2113_; lean_object* v_res_2114_; 
v_cleanupAnnotations_boxed_2113_ = lean_unbox(v_cleanupAnnotations_2107_);
v_res_2114_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2104_, v_type_2105_, v_k_2106_, v_cleanupAnnotations_boxed_2113_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2115_, size_t v_i_2116_, size_t v_stop_2117_, lean_object* v_b_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_usize_dec_eq(v_i_2116_, v_stop_2117_);
if (v___x_2124_ == 0)
{
size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_sub(v_i_2116_, v___x_2125_);
v___x_2127_ = lean_array_uget_borrowed(v_as_2115_, v___x_2126_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___x_2127_);
v___x_2128_ = lean_infer_type(v___x_2127_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_Meta_getLevel(v_a_2129_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_mkLevelIMax_x27(v_a_2131_, v_b_2118_);
v_i_2116_ = v___x_2126_;
v_b_2118_ = v___x_2132_;
goto _start;
}
else
{
lean_dec(v_b_2118_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2134_; 
v_a_2134_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2130_, 1);
v_i_2116_ = v___x_2126_;
v_b_2118_ = v_a_2134_;
goto _start;
}
else
{
return v___x_2130_;
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_b_2118_);
v_a_2136_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2128_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2128_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_b_2118_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
size_t v_i_boxed_2154_; size_t v_stop_boxed_2155_; lean_object* v_res_2156_; 
v_i_boxed_2154_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2145_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2157_, lean_object* v_e_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___y_2165_; lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Meta_getLevel(v_e_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
v___x_2186_ = lean_array_get_size(v_xs_2157_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_nat_dec_lt(v___x_2187_, v___x_2186_);
if (v___x_2188_ == 0)
{
lean_dec(v_a_2185_);
v___y_2165_ = v___x_2184_;
goto v___jp_2164_;
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref_known(v___x_2184_, 1);
v___x_2189_ = lean_usize_of_nat(v___x_2186_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2157_, v___x_2189_, v___x_2190_, v_a_2185_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v___y_2165_ = v___x_2191_;
goto v___jp_2164_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_a_2192_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2184_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2184_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
v___jp_2164_:
{
if (lean_obj_tag(v___y_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2175_; 
v_a_2166_ = lean_ctor_get(v___y_2165_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___y_2165_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2168_ = v___y_2165_;
v_isShared_2169_ = v_isSharedCheck_2175_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___y_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2175_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = l_Lean_Level_normalize(v_a_2166_);
lean_dec(v_a_2166_);
v___x_2171_ = l_Lean_mkSort(v___x_2170_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2171_);
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v___y_2165_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___y_2165_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___y_2165_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___y_2165_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2200_, lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2200_, v_e_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_xs_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___f_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v___f_2215_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2216_ = 0;
v___x_2217_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2209_, v___f_2215_, v___x_2216_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2225_, lean_object* v_k_2226_, uint8_t v_cleanupAnnotations_2227_, uint8_t v_preserveNondepLet_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___f_2234_; uint8_t v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2234_, 0, v_k_2226_);
v___x_2235_ = 1;
v___x_2236_ = 0;
v___x_2237_ = lean_box(0);
v___x_2238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2225_, v___x_2235_, v___x_2235_, v_preserveNondepLet_2228_, v___x_2236_, v___x_2237_, v___f_2234_, v_cleanupAnnotations_2227_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
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
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2255_, lean_object* v_k_2256_, lean_object* v_cleanupAnnotations_2257_, lean_object* v_preserveNondepLet_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2264_; uint8_t v_preserveNondepLet_boxed_2265_; lean_object* v_res_2266_; 
v_cleanupAnnotations_boxed_2264_ = lean_unbox(v_cleanupAnnotations_2257_);
v_preserveNondepLet_boxed_2265_ = lean_unbox(v_preserveNondepLet_2258_);
v_res_2266_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2255_, v_k_2256_, v_cleanupAnnotations_boxed_2264_, v_preserveNondepLet_boxed_2265_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2267_, lean_object* v_e_2268_, lean_object* v_k_2269_, uint8_t v_cleanupAnnotations_2270_, uint8_t v_preserveNondepLet_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2268_, v_k_2269_, v_cleanupAnnotations_2270_, v_preserveNondepLet_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2278_, lean_object* v_e_2279_, lean_object* v_k_2280_, lean_object* v_cleanupAnnotations_2281_, lean_object* v_preserveNondepLet_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2288_; uint8_t v_preserveNondepLet_boxed_2289_; lean_object* v_res_2290_; 
v_cleanupAnnotations_boxed_2288_ = lean_unbox(v_cleanupAnnotations_2281_);
v_preserveNondepLet_boxed_2289_ = lean_unbox(v_preserveNondepLet_2282_);
v_res_2290_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2278_, v_e_2279_, v_k_2280_, v_cleanupAnnotations_boxed_2288_, v_preserveNondepLet_boxed_2289_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2291_, lean_object* v_e_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
v___x_2298_ = lean_infer_type(v_e_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; uint8_t v___x_2300_; uint8_t v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = 0;
v___x_2301_ = 1;
v___x_2302_ = 1;
v___x_2303_ = l_Lean_Meta_mkForallFVars(v_xs_2291_, v_a_2299_, v___x_2300_, v___x_2301_, v___x_2300_, v___x_2302_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2303_;
}
else
{
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2304_, lean_object* v_e_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2304_, v_e_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v_xs_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___f_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; 
v___f_2319_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2320_ = 0;
v___x_2321_ = 1;
v___x_2322_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2313_, v___f_2319_, v___x_2320_, v___x_2321_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2329_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2332_ = l_Lean_stringToMessageData(v___x_2331_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2342_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2343_ = l_Lean_MessageData_ofName(v_mvarId_2336_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2346_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2355_, lean_object* v_mvarId_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_mvarId_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2363_, v_mvarId_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v_mctx_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_st_ref_get(v_a_2373_);
v_mctx_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_mctx_2378_);
lean_dec(v___x_2377_);
v___x_2379_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2378_, v_mvarId_2371_);
lean_dec_ref(v_mctx_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2380_;
}
else
{
lean_object* v_val_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_mvarId_2371_);
v_val_2381_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2383_ = v___x_2379_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_val_2381_);
lean_dec(v___x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_type_2385_; lean_object* v___x_2387_; 
v_type_2385_ = lean_ctor_get(v_val_2381_, 2);
lean_inc_ref(v_type_2385_);
lean_dec(v_val_2381_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set_tag(v___x_2383_, 0);
lean_ctor_set(v___x_2383_, 0, v_type_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_type_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_lctx_2402_; lean_object* v___x_2403_; 
v_lctx_2402_ = lean_ctor_get(v_a_2398_, 2);
lean_inc(v_fvarId_2397_);
lean_inc_ref(v_lctx_2402_);
v___x_2403_ = lean_local_ctx_find(v_lctx_2402_, v_fvarId_2397_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2397_, v_a_2399_, v_a_2400_);
return v___x_2404_;
}
else
{
lean_object* v_val_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_fvarId_2397_);
v_val_2405_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2407_ = v___x_2403_;
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_val_2405_);
lean_dec(v___x_2403_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = l_Lean_LocalDecl_type(v_val_2405_);
lean_dec(v_val_2405_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2420_, v_a_2421_, v_a_2423_, v_a_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
return v_res_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_instMonadEIO___redArg();
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2436_ = l_StateRefT_x27_instMonad___redArg(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_instMonadExceptOfEIO___redArg();
return v___x_2439_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___f_2441_; 
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2441_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2441_, 0, v___x_2440_);
return v___f_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___f_2443_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2443_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2443_, 0, v___x_2442_);
return v___f_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; 
v___f_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2445_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___f_2445_);
lean_ctor_set(v___x_2446_, 1, v___f_2444_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___f_2448_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2448_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2448_, 0, v___x_2447_);
return v___f_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___f_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2450_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2450_, 0, v___x_2449_);
return v___f_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; 
v___f_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2452_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___f_2452_);
lean_ctor_set(v___x_2453_, 1, v___f_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2456_, lean_object* v_inferType_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
uint8_t v_cacheInferType_2502_; 
v_cacheInferType_2502_ = lean_ctor_get_uint8(v_a_2458_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2502_ == 0)
{
lean_dec_ref(v_e_2456_);
goto v___jp_2463_;
}
else
{
uint8_t v___x_2503_; 
v___x_2503_ = l_Lean_Expr_hasMVar(v_e_2456_);
if (v___x_2503_ == 0)
{
lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___f_2504_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2505_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2506_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2456_, v_a_2458_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2604_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2604_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2604_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2551_; lean_object* v_cache_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2599_; 
v___x_2551_ = lean_st_ref_get(v_a_2459_);
v_cache_2552_ = lean_ctor_get(v___x_2551_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; lean_object* v_unused_2603_; 
v_unused_2600_ = lean_ctor_get(v___x_2551_, 4);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v___x_2551_, 3);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v___x_2551_, 2);
lean_dec(v_unused_2602_);
v_unused_2603_ = lean_ctor_get(v___x_2551_, 0);
lean_dec(v_unused_2603_);
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2599_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_cache_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2599_;
goto v_resetjp_2553_;
}
v___jp_2511_:
{
lean_object* v___x_2512_; 
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2512_ = lean_apply_5(v_inferType_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, lean_box(0));
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; uint8_t v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
v___x_2514_ = l_Lean_Expr_hasMVar(v_a_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2549_; 
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2512_, 0);
lean_dec(v_unused_2550_);
v___x_2516_ = v___x_2512_;
v_isShared_2517_ = v_isSharedCheck_2549_;
goto v_resetjp_2515_;
}
else
{
lean_dec(v___x_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2549_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v_cache_2519_; lean_object* v_mctx_2520_; lean_object* v_zetaDeltaFVarIds_2521_; lean_object* v_postponed_2522_; lean_object* v_diag_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2548_; 
v___x_2518_ = lean_st_ref_take(v_a_2459_);
v_cache_2519_ = lean_ctor_get(v___x_2518_, 1);
v_mctx_2520_ = lean_ctor_get(v___x_2518_, 0);
v_zetaDeltaFVarIds_2521_ = lean_ctor_get(v___x_2518_, 2);
v_postponed_2522_ = lean_ctor_get(v___x_2518_, 3);
v_diag_2523_ = lean_ctor_get(v___x_2518_, 4);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2525_ = v___x_2518_;
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_diag_2523_);
lean_inc(v_postponed_2522_);
lean_inc(v_zetaDeltaFVarIds_2521_);
lean_inc(v_cache_2519_);
lean_inc(v_mctx_2520_);
lean_dec(v___x_2518_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_inferType_2527_; lean_object* v_funInfo_2528_; lean_object* v_synthInstance_2529_; lean_object* v_whnf_2530_; lean_object* v_defEqTrans_2531_; lean_object* v_defEqPerm_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2547_; 
v_inferType_2527_ = lean_ctor_get(v_cache_2519_, 0);
v_funInfo_2528_ = lean_ctor_get(v_cache_2519_, 1);
v_synthInstance_2529_ = lean_ctor_get(v_cache_2519_, 2);
v_whnf_2530_ = lean_ctor_get(v_cache_2519_, 3);
v_defEqTrans_2531_ = lean_ctor_get(v_cache_2519_, 4);
v_defEqPerm_2532_ = lean_ctor_get(v_cache_2519_, 5);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_cache_2519_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2534_ = v_cache_2519_;
v_isShared_2535_ = v_isSharedCheck_2547_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_defEqPerm_2532_);
lean_inc(v_defEqTrans_2531_);
lean_inc(v_whnf_2530_);
lean_inc(v_synthInstance_2529_);
lean_inc(v_funInfo_2528_);
lean_inc(v_inferType_2527_);
lean_dec(v_cache_2519_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2547_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_inc(v_a_2513_);
v___x_2536_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2504_, v___x_2505_, v_inferType_2527_, v_a_2507_, v_a_2513_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_funInfo_2528_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_synthInstance_2529_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_whnf_2530_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_defEqTrans_2531_);
lean_ctor_set(v_reuseFailAlloc_2546_, 5, v_defEqPerm_2532_);
v___x_2538_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2540_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2538_);
v___x_2540_ = v___x_2525_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_mctx_2520_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_zetaDeltaFVarIds_2521_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_postponed_2522_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_diag_2523_);
v___x_2540_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_st_ref_put(v_a_2459_, v___x_2540_);
if (v_isShared_2517_ == 0)
{
v___x_2543_ = v___x_2516_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2513_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2513_);
lean_dec(v_a_2507_);
return v___x_2512_;
}
}
else
{
lean_dec(v_a_2507_);
return v___x_2512_;
}
}
v_resetjp_2553_:
{
lean_object* v_inferType_2556_; lean_object* v___x_2557_; 
v_inferType_2556_ = lean_ctor_get(v_cache_2552_, 0);
lean_inc_ref(v_inferType_2556_);
lean_dec_ref(v_cache_2552_);
lean_inc(v_a_2507_);
v___x_2557_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2504_, v___x_2505_, v_inferType_2556_, v_a_2507_);
lean_dec_ref(v_inferType_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; lean_object* v_toApplicative_2559_; lean_object* v_toFunctor_2560_; lean_object* v_toSeq_2561_; lean_object* v_toSeqLeft_2562_; lean_object* v_toSeqRight_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2573_; 
lean_del_object(v___x_2509_);
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2559_ = lean_ctor_get(v___x_2558_, 0);
v_toFunctor_2560_ = lean_ctor_get(v_toApplicative_2559_, 0);
v_toSeq_2561_ = lean_ctor_get(v_toApplicative_2559_, 2);
v_toSeqLeft_2562_ = lean_ctor_get(v_toApplicative_2559_, 3);
v_toSeqRight_2563_ = lean_ctor_get(v_toApplicative_2559_, 4);
v___f_2564_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2565_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2560_, 2);
v___f_2566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2566_, 0, v_toFunctor_2560_);
v___f_2567_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2567_, 0, v_toFunctor_2560_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___f_2566_);
lean_ctor_set(v___x_2568_, 1, v___f_2567_);
lean_inc(v_toSeqRight_2563_);
v___f_2569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2569_, 0, v_toSeqRight_2563_);
lean_inc(v_toSeqLeft_2562_);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toSeqLeft_2562_);
lean_inc(v_toSeq_2561_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toSeq_2561_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 4, v___f_2569_);
lean_ctor_set(v___x_2554_, 3, v___f_2570_);
lean_ctor_set(v___x_2554_, 2, v___f_2571_);
lean_ctor_set(v___x_2554_, 1, v___f_2564_);
lean_ctor_set(v___x_2554_, 0, v___x_2568_);
v___x_2573_ = v___x_2554_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___f_2564_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v___f_2571_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v___f_2570_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v___f_2569_);
v___x_2573_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_toCold_2580_; lean_object* v_cancelTk_x3f_2581_; 
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v___f_2565_);
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2576_ = l_Lean_Core_instMonadRefCoreM;
v___x_2577_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2578_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2577_, v___x_2574_);
v___x_2579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2575_);
lean_ctor_set(v___x_2579_, 1, v___x_2576_);
lean_ctor_set(v___x_2579_, 2, v___x_2578_);
v_toCold_2580_ = lean_ctor_get(v_a_2460_, 0);
v_cancelTk_x3f_2581_ = lean_ctor_get(v_toCold_2580_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2581_) == 1)
{
lean_object* v_val_2582_; uint8_t v___x_2583_; 
v_val_2582_ = lean_ctor_get(v_cancelTk_x3f_2581_, 0);
v___x_2583_ = l_IO_CancelToken_isSet(v_val_2582_);
if (v___x_2583_ == 0)
{
lean_dec_ref_known(v___x_2579_, 3);
goto v___jp_2511_;
}
else
{
lean_object* v___x_2058__overap_2584_; lean_object* v___x_2585_; 
v___x_2058__overap_2584_ = l_Lean_throwInterruptException___redArg(v___x_2579_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2585_ = lean_apply_3(v___x_2058__overap_2584_, v_a_2460_, v_a_2461_, lean_box(0));
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
goto v___jp_2511_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_a_2507_);
lean_dec_ref(v_inferType_2457_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2579_, 3);
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_val_2595_; lean_object* v___x_2597_; 
lean_del_object(v___x_2554_);
lean_dec(v_a_2507_);
lean_dec_ref(v_inferType_2457_);
v_val_2595_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v___x_2557_, 1);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v_val_2595_);
v___x_2597_ = v___x_2509_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_val_2595_);
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
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_inferType_2457_);
v_a_2605_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2506_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2506_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_dec_ref(v_e_2456_);
goto v___jp_2463_;
}
}
v___jp_2463_:
{
lean_object* v___x_2464_; lean_object* v_toApplicative_2465_; lean_object* v_toFunctor_2466_; lean_object* v_toSeq_2467_; lean_object* v_toSeqLeft_2468_; lean_object* v_toSeqRight_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_toCold_2485_; lean_object* v_cancelTk_x3f_2486_; 
v___x_2464_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2465_ = lean_ctor_get(v___x_2464_, 0);
v_toFunctor_2466_ = lean_ctor_get(v_toApplicative_2465_, 0);
v_toSeq_2467_ = lean_ctor_get(v_toApplicative_2465_, 2);
v_toSeqLeft_2468_ = lean_ctor_get(v_toApplicative_2465_, 3);
v_toSeqRight_2469_ = lean_ctor_get(v_toApplicative_2465_, 4);
v___f_2470_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2471_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2466_, 2);
v___f_2472_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2472_, 0, v_toFunctor_2466_);
v___f_2473_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2473_, 0, v_toFunctor_2466_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___f_2472_);
lean_ctor_set(v___x_2474_, 1, v___f_2473_);
lean_inc(v_toSeqRight_2469_);
v___f_2475_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2475_, 0, v_toSeqRight_2469_);
lean_inc(v_toSeqLeft_2468_);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toSeqLeft_2468_);
lean_inc(v_toSeq_2467_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toSeq_2467_);
v___x_2478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2474_);
lean_ctor_set(v___x_2478_, 1, v___f_2470_);
lean_ctor_set(v___x_2478_, 2, v___f_2477_);
lean_ctor_set(v___x_2478_, 3, v___f_2476_);
lean_ctor_set(v___x_2478_, 4, v___f_2475_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___f_2471_);
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2481_ = l_Lean_Core_instMonadRefCoreM;
v___x_2482_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2483_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2482_, v___x_2479_);
v___x_2484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2480_);
lean_ctor_set(v___x_2484_, 1, v___x_2481_);
lean_ctor_set(v___x_2484_, 2, v___x_2483_);
v_toCold_2485_ = lean_ctor_get(v_a_2460_, 0);
v_cancelTk_x3f_2486_ = lean_ctor_get(v_toCold_2485_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2486_) == 1)
{
lean_object* v_val_2487_; uint8_t v___x_2488_; 
v_val_2487_ = lean_ctor_get(v_cancelTk_x3f_2486_, 0);
v___x_2488_ = l_IO_CancelToken_isSet(v_val_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_dec_ref_known(v___x_2484_, 3);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2489_ = lean_apply_5(v_inferType_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, lean_box(0));
return v___x_2489_;
}
else
{
lean_object* v___x_2031__overap_2490_; lean_object* v___x_2491_; 
v___x_2031__overap_2490_ = l_Lean_throwInterruptException___redArg(v___x_2484_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2491_ = lean_apply_3(v___x_2031__overap_2490_, v_a_2460_, v_a_2461_, lean_box(0));
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref_known(v___x_2491_, 1);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2492_ = lean_apply_5(v_inferType_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, lean_box(0));
return v___x_2492_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v_inferType_2457_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v___x_2501_; 
lean_dec_ref_known(v___x_2484_, 3);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
lean_inc(v_a_2459_);
lean_inc_ref(v_a_2458_);
v___x_2501_ = lean_apply_5(v_inferType_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, lean_box(0));
return v___x_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2613_, lean_object* v_inferType_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2613_, v_inferType_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = 2;
v___x_2622_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2675_; uint8_t v_beta_2676_; 
v___x_2675_ = l_Lean_Meta_Context_config(v___y_2624_);
v_beta_2676_ = lean_ctor_get_uint8(v___x_2675_, 13);
if (v_beta_2676_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_iota_2677_; 
v_iota_2677_ = lean_ctor_get_uint8(v___x_2675_, 12);
if (v_iota_2677_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zeta_2678_; 
v_zeta_2678_ = lean_ctor_get_uint8(v___x_2675_, 15);
if (v_zeta_2678_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zetaHave_2679_; 
v_zetaHave_2679_ = lean_ctor_get_uint8(v___x_2675_, 18);
if (v_zetaHave_2679_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zetaDelta_2680_; 
v_zetaDelta_2680_ = lean_ctor_get_uint8(v___x_2675_, 16);
if (v_zetaDelta_2680_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_etaStruct_2681_; uint8_t v_proj_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_etaStruct_2681_ = lean_ctor_get_uint8(v___x_2675_, 10);
v_proj_2682_ = lean_ctor_get_uint8(v___x_2675_, 14);
lean_dec_ref(v___x_2675_);
v___x_2683_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_2682_);
v___x_2684_ = lean_obj_once(&l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0, &l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withInferTypeConfig___redArg___lam__0___closed__0);
v___x_2685_ = lean_nat_dec_eq(v___x_2683_, v___x_2684_);
lean_dec(v___x_2683_);
if (v___x_2685_ == 0)
{
goto v___jp_2629_;
}
else
{
uint8_t v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = 0;
v___x_2687_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2681_, v___x_2686_);
if (v___x_2687_ == 0)
{
goto v___jp_2629_;
}
else
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_apply_5(v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, lean_box(0));
return v___x_2688_;
}
}
}
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2630_; uint8_t v_foApprox_2631_; uint8_t v_ctxApprox_2632_; uint8_t v_quasiPatternApprox_2633_; uint8_t v_constApprox_2634_; uint8_t v_isDefEqStuckEx_2635_; uint8_t v_unificationHints_2636_; uint8_t v_proofIrrelevance_2637_; uint8_t v_assignSyntheticOpaque_2638_; uint8_t v_offsetCnstrs_2639_; uint8_t v_transparency_2640_; uint8_t v_univApprox_2641_; uint8_t v_zetaUnused_2642_; uint8_t v_canUnfoldPredicateConfig_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2674_; 
v___x_2630_ = l_Lean_Meta_Context_config(v___y_2624_);
v_foApprox_2631_ = lean_ctor_get_uint8(v___x_2630_, 0);
v_ctxApprox_2632_ = lean_ctor_get_uint8(v___x_2630_, 1);
v_quasiPatternApprox_2633_ = lean_ctor_get_uint8(v___x_2630_, 2);
v_constApprox_2634_ = lean_ctor_get_uint8(v___x_2630_, 3);
v_isDefEqStuckEx_2635_ = lean_ctor_get_uint8(v___x_2630_, 4);
v_unificationHints_2636_ = lean_ctor_get_uint8(v___x_2630_, 5);
v_proofIrrelevance_2637_ = lean_ctor_get_uint8(v___x_2630_, 6);
v_assignSyntheticOpaque_2638_ = lean_ctor_get_uint8(v___x_2630_, 7);
v_offsetCnstrs_2639_ = lean_ctor_get_uint8(v___x_2630_, 8);
v_transparency_2640_ = lean_ctor_get_uint8(v___x_2630_, 9);
v_univApprox_2641_ = lean_ctor_get_uint8(v___x_2630_, 11);
v_zetaUnused_2642_ = lean_ctor_get_uint8(v___x_2630_, 17);
v_canUnfoldPredicateConfig_2643_ = lean_ctor_get_uint8(v___x_2630_, 19);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2645_ = v___x_2630_;
v_isShared_2646_ = v_isSharedCheck_2674_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v___x_2630_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2674_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint8_t v___x_2647_; uint8_t v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2651_; 
v___x_2647_ = 1;
v___x_2648_ = 0;
v___x_2649_ = 2;
if (v_isShared_2646_ == 0)
{
v___x_2651_ = v___x_2645_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 0, v_foApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 1, v_ctxApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 2, v_quasiPatternApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 3, v_constApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 4, v_isDefEqStuckEx_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 5, v_unificationHints_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 6, v_proofIrrelevance_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 7, v_assignSyntheticOpaque_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 8, v_offsetCnstrs_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 9, v_transparency_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 11, v_univApprox_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 17, v_zetaUnused_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 19, v_canUnfoldPredicateConfig_2643_);
v___x_2651_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
uint8_t v_trackZetaDelta_2652_; lean_object* v_zetaDeltaSet_2653_; lean_object* v_lctx_2654_; lean_object* v_localInstances_2655_; lean_object* v_defEqCtx_x3f_2656_; lean_object* v_synthPendingDepth_2657_; lean_object* v_customCanUnfoldPredicate_x3f_2658_; uint8_t v_univApprox_2659_; uint8_t v_inTypeClassResolution_2660_; uint8_t v_cacheInferType_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2671_; 
lean_ctor_set_uint8(v___x_2651_, 10, v___x_2648_);
lean_ctor_set_uint8(v___x_2651_, 12, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 13, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 14, v___x_2649_);
lean_ctor_set_uint8(v___x_2651_, 15, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 16, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 18, v___x_2647_);
v_trackZetaDelta_2652_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7);
v_zetaDeltaSet_2653_ = lean_ctor_get(v___y_2624_, 1);
v_lctx_2654_ = lean_ctor_get(v___y_2624_, 2);
v_localInstances_2655_ = lean_ctor_get(v___y_2624_, 3);
v_defEqCtx_x3f_2656_ = lean_ctor_get(v___y_2624_, 4);
v_synthPendingDepth_2657_ = lean_ctor_get(v___y_2624_, 5);
v_customCanUnfoldPredicate_x3f_2658_ = lean_ctor_get(v___y_2624_, 6);
v_univApprox_2659_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2660_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 2);
v_cacheInferType_2661_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 3);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___y_2624_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___y_2624_, 0);
lean_dec(v_unused_2672_);
v___x_2663_ = v___y_2624_;
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2658_);
lean_inc(v_synthPendingDepth_2657_);
lean_inc(v_defEqCtx_x3f_2656_);
lean_inc(v_localInstances_2655_);
lean_inc(v_lctx_2654_);
lean_inc(v_zetaDeltaSet_2653_);
lean_dec(v___y_2624_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint64_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2651_);
v___x_2666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2666_, 0, v___x_2651_);
lean_ctor_set_uint64(v___x_2666_, sizeof(void*)*1, v___x_2665_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2666_);
v___x_2668_ = v___x_2663_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_zetaDeltaSet_2653_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_lctx_2654_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_localInstances_2655_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_defEqCtx_x3f_2656_);
lean_ctor_set(v_reuseFailAlloc_2670_, 5, v_synthPendingDepth_2657_);
lean_ctor_set(v_reuseFailAlloc_2670_, 6, v_customCanUnfoldPredicate_x3f_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7, v_trackZetaDelta_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 1, v_univApprox_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 3, v_cacheInferType_2661_);
v___x_2668_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_apply_5(v_x_2623_, v___x_2668_, v___y_2625_, v___y_2626_, v___y_2627_, lean_box(0));
return v___x_2669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___y_2703_; lean_object* v___x_2720_; uint8_t v_transparency_2721_; uint8_t v___x_2722_; uint8_t v___x_2723_; 
v___x_2720_ = l_Lean_Meta_Context_config(v_a_2697_);
v_transparency_2721_ = lean_ctor_get_uint8(v___x_2720_, 9);
lean_dec_ref(v___x_2720_);
v___x_2722_ = 1;
v___x_2723_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; 
lean_inc(v_a_2700_);
lean_inc_ref(v_a_2699_);
lean_inc(v_a_2698_);
lean_inc_ref(v_a_2697_);
v___x_2724_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2703_ = v___x_2724_;
goto v___jp_2702_;
}
else
{
lean_object* v_keyedConfig_2725_; uint8_t v_trackZetaDelta_2726_; lean_object* v_zetaDeltaSet_2727_; lean_object* v_lctx_2728_; lean_object* v_localInstances_2729_; lean_object* v_defEqCtx_x3f_2730_; lean_object* v_synthPendingDepth_2731_; lean_object* v_customCanUnfoldPredicate_x3f_2732_; uint8_t v_univApprox_2733_; uint8_t v_inTypeClassResolution_2734_; uint8_t v_cacheInferType_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_keyedConfig_2725_ = lean_ctor_get(v_a_2697_, 0);
v_trackZetaDelta_2726_ = lean_ctor_get_uint8(v_a_2697_, sizeof(void*)*7);
v_zetaDeltaSet_2727_ = lean_ctor_get(v_a_2697_, 1);
v_lctx_2728_ = lean_ctor_get(v_a_2697_, 2);
v_localInstances_2729_ = lean_ctor_get(v_a_2697_, 3);
v_defEqCtx_x3f_2730_ = lean_ctor_get(v_a_2697_, 4);
v_synthPendingDepth_2731_ = lean_ctor_get(v_a_2697_, 5);
v_customCanUnfoldPredicate_x3f_2732_ = lean_ctor_get(v_a_2697_, 6);
v_univApprox_2733_ = lean_ctor_get_uint8(v_a_2697_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2734_ = lean_ctor_get_uint8(v_a_2697_, sizeof(void*)*7 + 2);
v_cacheInferType_2735_ = lean_ctor_get_uint8(v_a_2697_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2725_);
v___x_2736_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2722_, v_keyedConfig_2725_);
lean_inc(v_customCanUnfoldPredicate_x3f_2732_);
lean_inc(v_synthPendingDepth_2731_);
lean_inc(v_defEqCtx_x3f_2730_);
lean_inc_ref(v_localInstances_2729_);
lean_inc_ref(v_lctx_2728_);
lean_inc(v_zetaDeltaSet_2727_);
v___x_2737_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_zetaDeltaSet_2727_);
lean_ctor_set(v___x_2737_, 2, v_lctx_2728_);
lean_ctor_set(v___x_2737_, 3, v_localInstances_2729_);
lean_ctor_set(v___x_2737_, 4, v_defEqCtx_x3f_2730_);
lean_ctor_set(v___x_2737_, 5, v_synthPendingDepth_2731_);
lean_ctor_set(v___x_2737_, 6, v_customCanUnfoldPredicate_x3f_2732_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*7, v_trackZetaDelta_2726_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*7 + 1, v_univApprox_2733_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2734_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*7 + 3, v_cacheInferType_2735_);
lean_inc(v_a_2700_);
lean_inc_ref(v_a_2699_);
lean_inc(v_a_2698_);
v___x_2738_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2696_, v___x_2737_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2703_ = v___x_2738_;
goto v___jp_2702_;
}
v___jp_2702_:
{
if (lean_obj_tag(v___y_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___y_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___y_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___y_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___y_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_a_2712_ = lean_ctor_get(v___y_2703_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___y_2703_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___y_2703_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___y_2703_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2746_, lean_object* v_x_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___y_2754_; lean_object* v___x_2771_; uint8_t v_transparency_2772_; uint8_t v___x_2773_; uint8_t v___x_2774_; 
v___x_2771_ = l_Lean_Meta_Context_config(v_a_2748_);
v_transparency_2772_ = lean_ctor_get_uint8(v___x_2771_, 9);
lean_dec_ref(v___x_2771_);
v___x_2773_ = 1;
v___x_2774_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_inc(v_a_2751_);
lean_inc_ref(v_a_2750_);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
v___x_2775_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
v___y_2754_ = v___x_2775_;
goto v___jp_2753_;
}
else
{
lean_object* v_keyedConfig_2776_; uint8_t v_trackZetaDelta_2777_; lean_object* v_zetaDeltaSet_2778_; lean_object* v_lctx_2779_; lean_object* v_localInstances_2780_; lean_object* v_defEqCtx_x3f_2781_; lean_object* v_synthPendingDepth_2782_; lean_object* v_customCanUnfoldPredicate_x3f_2783_; uint8_t v_univApprox_2784_; uint8_t v_inTypeClassResolution_2785_; uint8_t v_cacheInferType_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_keyedConfig_2776_ = lean_ctor_get(v_a_2748_, 0);
v_trackZetaDelta_2777_ = lean_ctor_get_uint8(v_a_2748_, sizeof(void*)*7);
v_zetaDeltaSet_2778_ = lean_ctor_get(v_a_2748_, 1);
v_lctx_2779_ = lean_ctor_get(v_a_2748_, 2);
v_localInstances_2780_ = lean_ctor_get(v_a_2748_, 3);
v_defEqCtx_x3f_2781_ = lean_ctor_get(v_a_2748_, 4);
v_synthPendingDepth_2782_ = lean_ctor_get(v_a_2748_, 5);
v_customCanUnfoldPredicate_x3f_2783_ = lean_ctor_get(v_a_2748_, 6);
v_univApprox_2784_ = lean_ctor_get_uint8(v_a_2748_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2785_ = lean_ctor_get_uint8(v_a_2748_, sizeof(void*)*7 + 2);
v_cacheInferType_2786_ = lean_ctor_get_uint8(v_a_2748_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2776_);
v___x_2787_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2773_, v_keyedConfig_2776_);
lean_inc(v_customCanUnfoldPredicate_x3f_2783_);
lean_inc(v_synthPendingDepth_2782_);
lean_inc(v_defEqCtx_x3f_2781_);
lean_inc_ref(v_localInstances_2780_);
lean_inc_ref(v_lctx_2779_);
lean_inc(v_zetaDeltaSet_2778_);
v___x_2788_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_zetaDeltaSet_2778_);
lean_ctor_set(v___x_2788_, 2, v_lctx_2779_);
lean_ctor_set(v___x_2788_, 3, v_localInstances_2780_);
lean_ctor_set(v___x_2788_, 4, v_defEqCtx_x3f_2781_);
lean_ctor_set(v___x_2788_, 5, v_synthPendingDepth_2782_);
lean_ctor_set(v___x_2788_, 6, v_customCanUnfoldPredicate_x3f_2783_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*7, v_trackZetaDelta_2777_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*7 + 1, v_univApprox_2784_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2785_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*7 + 3, v_cacheInferType_2786_);
lean_inc(v_a_2751_);
lean_inc_ref(v_a_2750_);
lean_inc(v_a_2749_);
v___x_2789_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2747_, v___x_2788_, v_a_2749_, v_a_2750_, v_a_2751_);
v___y_2754_ = v___x_2789_;
goto v___jp_2753_;
}
v___jp_2753_:
{
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___y_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___y_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___y_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___y_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v___y_2754_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___y_2754_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___y_2754_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___y_2754_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2790_, lean_object* v_x_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2790_, v_x_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
return v_res_2797_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_box(0);
v___x_2799_ = l_Lean_interruptExceptionId;
v___x_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v_ks_2820_; lean_object* v_vs_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2850_; 
v_ks_2820_ = lean_ctor_get(v_x_2816_, 0);
v_vs_2821_ = lean_ctor_get(v_x_2816_, 1);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2816_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2823_ = v_x_2816_;
v_isShared_2824_ = v_isSharedCheck_2850_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_vs_2821_);
lean_inc(v_ks_2820_);
lean_dec(v_x_2816_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2850_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v___y_2826_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_array_get_size(v_ks_2820_);
v___x_2839_ = lean_nat_dec_lt(v_x_2817_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_del_object(v___x_2823_);
lean_dec(v_x_2817_);
v___x_2840_ = lean_array_push(v_ks_2820_, v_x_2818_);
v___x_2841_ = lean_array_push(v_vs_2821_, v_x_2819_);
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
return v___x_2842_;
}
else
{
lean_object* v_expr_2843_; uint64_t v_configKey_2844_; lean_object* v_k_x27_2845_; lean_object* v_expr_2846_; uint64_t v_configKey_2847_; uint8_t v___x_2848_; 
v_expr_2843_ = lean_ctor_get(v_x_2818_, 0);
v_configKey_2844_ = lean_ctor_get_uint64(v_x_2818_, sizeof(void*)*1);
v_k_x27_2845_ = lean_array_fget_borrowed(v_ks_2820_, v_x_2817_);
v_expr_2846_ = lean_ctor_get(v_k_x27_2845_, 0);
v_configKey_2847_ = lean_ctor_get_uint64(v_k_x27_2845_, sizeof(void*)*1);
v___x_2848_ = lean_expr_equal(v_expr_2843_, v_expr_2846_);
if (v___x_2848_ == 0)
{
v___y_2826_ = v___x_2848_;
goto v___jp_2825_;
}
else
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_uint64_dec_eq(v_configKey_2844_, v_configKey_2847_);
v___y_2826_ = v___x_2849_;
goto v___jp_2825_;
}
}
v___jp_2825_:
{
if (v___y_2826_ == 0)
{
lean_object* v___x_2828_; 
if (v_isShared_2824_ == 0)
{
v___x_2828_ = v___x_2823_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_ks_2820_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_vs_2821_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_add(v_x_2817_, v___x_2829_);
lean_dec(v_x_2817_);
v_x_2816_ = v___x_2828_;
v_x_2817_ = v___x_2830_;
goto _start;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2833_ = lean_array_fset(v_ks_2820_, v_x_2817_, v_x_2818_);
v___x_2834_ = lean_array_fset(v_vs_2821_, v_x_2817_, v_x_2819_);
lean_dec(v_x_2817_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2834_);
lean_ctor_set(v___x_2823_, 0, v___x_2833_);
v___x_2836_ = v___x_2823_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2851_, lean_object* v_k_2852_, lean_object* v_v_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_unsigned_to_nat(0u);
v___x_2855_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2851_, v___x_2854_, v_k_2852_, v_v_2853_);
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
v___x_2930_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
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
size_t v_x_2794__boxed_2969_; size_t v_x_2795__boxed_2970_; lean_object* v_res_2971_; 
v_x_2794__boxed_2969_ = lean_unbox_usize(v_x_2965_);
lean_dec(v_x_2965_);
v_x_2795__boxed_2970_ = lean_unbox_usize(v_x_2966_);
lean_dec(v_x_2966_);
v_res_2971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2964_, v_x_2794__boxed_2969_, v_x_2795__boxed_2970_, v_x_2967_, v_x_2968_);
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
size_t v_x_2998__boxed_3041_; lean_object* v_res_3042_; 
v_x_2998__boxed_3041_ = lean_unbox_usize(v_x_3039_);
lean_dec(v_x_3039_);
v_res_3042_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3038_, v_x_2998__boxed_3041_, v_x_3040_);
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
size_t v_x_4036__boxed_3594_; size_t v_x_4037__boxed_3595_; lean_object* v_res_3596_; 
v_x_4036__boxed_3594_ = lean_unbox_usize(v_x_3590_);
lean_dec(v_x_3590_);
v_x_4037__boxed_3595_ = lean_unbox_usize(v_x_3591_);
lean_dec(v_x_3591_);
v_res_3596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3588_, v_x_3589_, v_x_4036__boxed_3594_, v_x_4037__boxed_3595_, v_x_3592_, v_x_3593_);
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
size_t v_x_4053__boxed_3606_; lean_object* v_res_3607_; 
v_x_4053__boxed_3606_ = lean_unbox_usize(v_x_3604_);
lean_dec(v_x_3604_);
v_res_3607_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3602_, v_x_3603_, v_x_4053__boxed_3606_, v_x_3605_);
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
lean_object* v___y_3766_; lean_object* v_toCold_3783_; lean_object* v_currRecDepth_3784_; lean_object* v_ref_3785_; uint16_t v_optionFlags_3786_; uint8_t v_suppressElabErrors_3787_; uint8_t v_isRecordingDeps_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3828_; 
v_toCold_3783_ = lean_ctor_get(v_a_3762_, 0);
v_currRecDepth_3784_ = lean_ctor_get(v_a_3762_, 1);
v_ref_3785_ = lean_ctor_get(v_a_3762_, 2);
v_optionFlags_3786_ = lean_ctor_get_uint16(v_a_3762_, sizeof(void*)*3);
v_suppressElabErrors_3787_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3788_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*3 + 3);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3790_ = v_a_3762_;
v_isShared_3791_ = v_isSharedCheck_3828_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_ref_3785_);
lean_inc(v_currRecDepth_3784_);
lean_inc(v_toCold_3783_);
lean_dec(v_a_3762_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3828_;
goto v_resetjp_3789_;
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
v_resetjp_3789_:
{
lean_object* v_maxRecDepth_3792_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_maxRecDepth_3792_ = lean_ctor_get(v_toCold_3783_, 3);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_nat_dec_eq(v_maxRecDepth_3792_, v___x_3824_);
if (v___x_3825_ == 0)
{
uint8_t v___x_3826_; 
v___x_3826_ = lean_nat_dec_eq(v_currRecDepth_3784_, v_maxRecDepth_3792_);
if (v___x_3826_ == 0)
{
goto v___jp_3793_;
}
else
{
lean_object* v___x_3827_; 
lean_del_object(v___x_3790_);
lean_dec(v_currRecDepth_3784_);
lean_dec_ref(v_toCold_3783_);
lean_dec(v_a_3763_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec_ref(v_e_3759_);
v___x_3827_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3785_);
return v___x_3827_;
}
}
else
{
goto v___jp_3793_;
}
v___jp_3793_:
{
lean_object* v___x_3794_; uint8_t v_transparency_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3794_ = l_Lean_Meta_Context_config(v_a_3760_);
v_transparency_3795_ = lean_ctor_get_uint8(v___x_3794_, 9);
lean_dec_ref(v___x_3794_);
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_add(v_currRecDepth_3784_, v___x_3796_);
lean_dec(v_currRecDepth_3784_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 1, v___x_3797_);
v___x_3799_ = v___x_3790_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_toCold_3783_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3823_, 2, v_ref_3785_);
lean_ctor_set_uint16(v_reuseFailAlloc_3823_, sizeof(void*)*3, v_optionFlags_3786_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*3 + 2, v_suppressElabErrors_3787_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*3 + 3, v_isRecordingDeps_3788_);
v___x_3799_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
uint8_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = 1;
v___x_3801_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3795_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3759_, v_a_3760_, v_a_3761_, v___x_3799_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v___x_3799_);
lean_dec(v_a_3761_);
v___y_3766_ = v___x_3802_;
goto v___jp_3765_;
}
else
{
lean_object* v_keyedConfig_3803_; uint8_t v_trackZetaDelta_3804_; lean_object* v_zetaDeltaSet_3805_; lean_object* v_lctx_3806_; lean_object* v_localInstances_3807_; lean_object* v_defEqCtx_x3f_3808_; lean_object* v_synthPendingDepth_3809_; lean_object* v_customCanUnfoldPredicate_x3f_3810_; uint8_t v_univApprox_3811_; uint8_t v_inTypeClassResolution_3812_; uint8_t v_cacheInferType_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3822_; 
v_keyedConfig_3803_ = lean_ctor_get(v_a_3760_, 0);
v_trackZetaDelta_3804_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7);
v_zetaDeltaSet_3805_ = lean_ctor_get(v_a_3760_, 1);
v_lctx_3806_ = lean_ctor_get(v_a_3760_, 2);
v_localInstances_3807_ = lean_ctor_get(v_a_3760_, 3);
v_defEqCtx_x3f_3808_ = lean_ctor_get(v_a_3760_, 4);
v_synthPendingDepth_3809_ = lean_ctor_get(v_a_3760_, 5);
v_customCanUnfoldPredicate_x3f_3810_ = lean_ctor_get(v_a_3760_, 6);
v_univApprox_3811_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3812_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 2);
v_cacheInferType_3813_ = lean_ctor_get_uint8(v_a_3760_, sizeof(void*)*7 + 3);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_a_3760_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3815_ = v_a_3760_;
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3810_);
lean_inc(v_synthPendingDepth_3809_);
lean_inc(v_defEqCtx_x3f_3808_);
lean_inc(v_localInstances_3807_);
lean_inc(v_lctx_3806_);
lean_inc(v_zetaDeltaSet_3805_);
lean_inc(v_keyedConfig_3803_);
lean_dec(v_a_3760_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3800_, v_keyedConfig_3803_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_zetaDeltaSet_3805_);
lean_ctor_set(v_reuseFailAlloc_3821_, 2, v_lctx_3806_);
lean_ctor_set(v_reuseFailAlloc_3821_, 3, v_localInstances_3807_);
lean_ctor_set(v_reuseFailAlloc_3821_, 4, v_defEqCtx_x3f_3808_);
lean_ctor_set(v_reuseFailAlloc_3821_, 5, v_synthPendingDepth_3809_);
lean_ctor_set(v_reuseFailAlloc_3821_, 6, v_customCanUnfoldPredicate_x3f_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*7, v_trackZetaDelta_3804_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*7 + 1, v_univApprox_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3821_, sizeof(void*)*7 + 3, v_cacheInferType_3813_);
v___x_3819_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3759_, v___x_3819_, v_a_3761_, v___x_3799_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v___x_3799_);
lean_dec(v_a_3761_);
v___y_3766_ = v___x_3820_;
goto v___jp_3765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = lean_infer_type(v_e_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3836_){
_start:
{
switch(lean_obj_tag(v_x_3836_))
{
case 0:
{
uint8_t v___x_3837_; 
v___x_3837_ = 1;
return v___x_3837_;
}
case 2:
{
lean_object* v_a_3838_; lean_object* v_a_3839_; uint8_t v___x_3840_; 
v_a_3838_ = lean_ctor_get(v_x_3836_, 0);
v_a_3839_ = lean_ctor_get(v_x_3836_, 1);
v___x_3840_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3838_);
if (v___x_3840_ == 0)
{
return v___x_3840_;
}
else
{
v_x_3836_ = v_a_3839_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v_x_3836_, 1);
v_x_3836_ = v_a_3842_;
goto _start;
}
default: 
{
uint8_t v___x_3844_; 
v___x_3844_ = 0;
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3845_){
_start:
{
uint8_t v_res_3846_; lean_object* v_r_3847_; 
v_res_3846_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3845_);
lean_dec(v_x_3845_);
v_r_3847_ = lean_box(v_res_3846_);
return v_r_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; lean_object* v_mctx_3852_; lean_object* v___x_3853_; lean_object* v_fst_3854_; lean_object* v_snd_3855_; lean_object* v___x_3856_; lean_object* v_cache_3857_; lean_object* v_zetaDeltaFVarIds_3858_; lean_object* v_postponed_3859_; lean_object* v_diag_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3869_; 
v___x_3851_ = lean_st_ref_get(v___y_3849_);
v_mctx_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc_ref(v_mctx_3852_);
lean_dec(v___x_3851_);
v___x_3853_ = lean_instantiate_level_mvars(v_mctx_3852_, v_l_3848_);
v_fst_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_fst_3854_);
v_snd_3855_ = lean_ctor_get(v___x_3853_, 1);
lean_inc(v_snd_3855_);
lean_dec_ref(v___x_3853_);
v___x_3856_ = lean_st_ref_take(v___y_3849_);
v_cache_3857_ = lean_ctor_get(v___x_3856_, 1);
v_zetaDeltaFVarIds_3858_ = lean_ctor_get(v___x_3856_, 2);
v_postponed_3859_ = lean_ctor_get(v___x_3856_, 3);
v_diag_3860_ = lean_ctor_get(v___x_3856_, 4);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; 
v_unused_3870_ = lean_ctor_get(v___x_3856_, 0);
lean_dec(v_unused_3870_);
v___x_3862_ = v___x_3856_;
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_diag_3860_);
lean_inc(v_postponed_3859_);
lean_inc(v_zetaDeltaFVarIds_3858_);
lean_inc(v_cache_3857_);
lean_dec(v___x_3856_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v_fst_3854_);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_fst_3854_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_cache_3857_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_zetaDeltaFVarIds_3858_);
lean_ctor_set(v_reuseFailAlloc_3868_, 3, v_postponed_3859_);
lean_ctor_set(v_reuseFailAlloc_3868_, 4, v_diag_3860_);
v___x_3865_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_st_ref_put(v___y_3849_, v___x_3865_);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v_snd_3855_);
return v___x_3867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3871_, v___y_3872_);
lean_dec(v___y_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3875_, v___y_3877_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3889_, lean_object* v_x_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
switch(lean_obj_tag(v_x_3889_))
{
case 3:
{
lean_object* v_u_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_u_3900_ = lean_ctor_get(v_x_3889_, 0);
lean_inc(v_u_3900_);
lean_dec_ref_known(v_x_3889_, 1);
v___x_3901_ = lean_unsigned_to_nat(0u);
v___x_3902_ = lean_nat_dec_eq(v_x_3890_, v___x_3901_);
lean_dec(v_x_3890_);
if (v___x_3902_ == 0)
{
lean_dec(v_u_3900_);
goto v___jp_3896_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3900_, v_a_3892_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3914_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3914_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
uint8_t v___x_3908_; uint8_t v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3908_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3904_);
lean_dec(v_a_3904_);
v___x_3909_ = l_Lean_Bool_toLBool(v___x_3908_);
v___x_3910_ = lean_box(v___x_3909_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3910_);
v___x_3912_ = v___x_3906_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
v_a_3915_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3903_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3903_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3923_; lean_object* v_zero_3924_; uint8_t v_isZero_3925_; 
v_body_3923_ = lean_ctor_get(v_x_3889_, 2);
lean_inc_ref(v_body_3923_);
lean_dec_ref_known(v_x_3889_, 3);
v_zero_3924_ = lean_unsigned_to_nat(0u);
v_isZero_3925_ = lean_nat_dec_eq(v_x_3890_, v_zero_3924_);
if (v_isZero_3925_ == 1)
{
uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
lean_dec_ref(v_body_3923_);
lean_dec(v_x_3890_);
v___x_3926_ = 0;
v___x_3927_ = lean_box(v___x_3926_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
else
{
lean_object* v_one_3929_; lean_object* v_n_3930_; 
v_one_3929_ = lean_unsigned_to_nat(1u);
v_n_3930_ = lean_nat_sub(v_x_3890_, v_one_3929_);
lean_dec(v_x_3890_);
v_x_3889_ = v_body_3923_;
v_x_3890_ = v_n_3930_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3932_; 
v_body_3932_ = lean_ctor_get(v_x_3889_, 3);
lean_inc_ref(v_body_3932_);
lean_dec_ref_known(v_x_3889_, 4);
v_x_3889_ = v_body_3932_;
goto _start;
}
case 10:
{
lean_object* v_expr_3934_; 
v_expr_3934_ = lean_ctor_get(v_x_3889_, 1);
lean_inc_ref(v_expr_3934_);
lean_dec_ref_known(v_x_3889_, 2);
v_x_3889_ = v_expr_3934_;
goto _start;
}
default: 
{
lean_dec(v_x_3890_);
lean_dec_ref(v_x_3889_);
goto v___jp_3896_;
}
}
v___jp_3896_:
{
uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = 2;
v___x_3898_ = lean_box(v___x_3897_);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3936_, lean_object* v_x_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3936_, v_x_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3944_, lean_object* v_x_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
switch(lean_obj_tag(v_x_3944_))
{
case 4:
{
lean_object* v_declName_3951_; lean_object* v_us_3952_; lean_object* v___x_3953_; 
v_declName_3951_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_declName_3951_);
v_us_3952_ = lean_ctor_get(v_x_3944_, 1);
lean_inc(v_us_3952_);
lean_dec_ref_known(v_x_3944_, 2);
v___x_3953_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3951_, v_us_3952_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3954_, v_x_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3955_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_x_3945_);
v_a_3956_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3953_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3953_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3964_; lean_object* v___x_3965_; 
v_fvarId_3964_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_fvarId_3964_);
lean_dec_ref_known(v_x_3944_, 1);
v___x_3965_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3964_, v_a_3946_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3966_, v_x_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3967_;
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v_x_3945_);
v_a_3968_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3965_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3965_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3976_; lean_object* v___x_3977_; 
v_mvarId_3976_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_mvarId_3976_);
lean_dec_ref_known(v_x_3944_, 1);
v___x_3977_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3976_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3979_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3978_, v_x_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3979_;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_x_3945_);
v_a_3980_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3977_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3977_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
case 5:
{
lean_object* v_fn_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_fn_3988_ = lean_ctor_get(v_x_3944_, 0);
lean_inc_ref(v_fn_3988_);
lean_dec_ref_known(v_x_3944_, 2);
v___x_3989_ = lean_unsigned_to_nat(1u);
v___x_3990_ = lean_nat_add(v_x_3945_, v___x_3989_);
lean_dec(v_x_3945_);
v_x_3944_ = v_fn_3988_;
v_x_3945_ = v___x_3990_;
goto _start;
}
case 10:
{
lean_object* v_expr_3992_; 
v_expr_3992_ = lean_ctor_get(v_x_3944_, 1);
lean_inc_ref(v_expr_3992_);
lean_dec_ref_known(v_x_3944_, 2);
v_x_3944_ = v_expr_3992_;
goto _start;
}
case 8:
{
lean_object* v_body_3994_; 
v_body_3994_ = lean_ctor_get(v_x_3944_, 3);
lean_inc_ref(v_body_3994_);
lean_dec_ref_known(v_x_3944_, 4);
v_x_3944_ = v_body_3994_;
goto _start;
}
case 6:
{
lean_object* v_body_3996_; lean_object* v_zero_3997_; uint8_t v_isZero_3998_; 
v_body_3996_ = lean_ctor_get(v_x_3944_, 2);
lean_inc_ref(v_body_3996_);
lean_dec_ref_known(v_x_3944_, 3);
v_zero_3997_ = lean_unsigned_to_nat(0u);
v_isZero_3998_ = lean_nat_dec_eq(v_x_3945_, v_zero_3997_);
if (v_isZero_3998_ == 1)
{
uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v_body_3996_);
lean_dec(v_x_3945_);
v___x_3999_ = 0;
v___x_4000_ = lean_box(v___x_3999_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
else
{
lean_object* v_one_4002_; lean_object* v_n_4003_; 
v_one_4002_ = lean_unsigned_to_nat(1u);
v_n_4003_ = lean_nat_sub(v_x_3945_, v_one_4002_);
lean_dec(v_x_3945_);
v_x_3944_ = v_body_3996_;
v_x_3945_ = v_n_4003_;
goto _start;
}
}
default: 
{
uint8_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v_x_3945_);
lean_dec_ref(v_x_3944_);
v___x_4005_ = 2;
v___x_4006_ = lean_box(v___x_4005_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4008_, lean_object* v_x_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4008_, v_x_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_a_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
switch(lean_obj_tag(v_x_4016_))
{
case 0:
{
uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec_ref_known(v_x_4016_, 1);
v___x_4022_ = 2;
v___x_4023_ = lean_box(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
case 1:
{
lean_object* v_fvarId_4025_; lean_object* v___x_4026_; 
v_fvarId_4025_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_fvarId_4025_);
lean_dec_ref_known(v_x_4016_, 1);
v___x_4026_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4025_, v_a_4017_, v_a_4019_, v_a_4020_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4027_, v___x_4028_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v___x_4029_;
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v_a_4030_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4026_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4026_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4038_; lean_object* v___x_4039_; 
v_mvarId_4038_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_mvarId_4038_);
lean_dec_ref_known(v_x_4016_, 1);
v___x_4039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4038_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
v___x_4041_ = lean_unsigned_to_nat(0u);
v___x_4042_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4040_, v___x_4041_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v___x_4042_;
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4039_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4039_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
case 4:
{
lean_object* v_declName_4051_; lean_object* v_us_4052_; lean_object* v___x_4053_; 
v_declName_4051_ = lean_ctor_get(v_x_4016_, 0);
lean_inc(v_declName_4051_);
v_us_4052_ = lean_ctor_get(v_x_4016_, 1);
lean_inc(v_us_4052_);
lean_dec_ref_known(v_x_4016_, 2);
v___x_4053_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4051_, v_us_4052_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4054_, v___x_4055_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v___x_4056_;
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
v_a_4057_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4053_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4053_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
case 5:
{
lean_object* v_fn_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_fn_4065_ = lean_ctor_get(v_x_4016_, 0);
lean_inc_ref(v_fn_4065_);
lean_dec_ref_known(v_x_4016_, 2);
v___x_4066_ = lean_unsigned_to_nat(1u);
v___x_4067_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4065_, v___x_4066_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
return v___x_4067_;
}
case 7:
{
lean_object* v_body_4068_; 
v_body_4068_ = lean_ctor_get(v_x_4016_, 2);
lean_inc_ref(v_body_4068_);
lean_dec_ref_known(v_x_4016_, 3);
v_x_4016_ = v_body_4068_;
goto _start;
}
case 8:
{
lean_object* v_body_4070_; 
v_body_4070_ = lean_ctor_get(v_x_4016_, 3);
lean_inc_ref(v_body_4070_);
lean_dec_ref_known(v_x_4016_, 4);
v_x_4016_ = v_body_4070_;
goto _start;
}
case 10:
{
lean_object* v_expr_4072_; 
v_expr_4072_ = lean_ctor_get(v_x_4016_, 1);
lean_inc_ref(v_expr_4072_);
lean_dec_ref_known(v_x_4016_, 2);
v_x_4016_ = v_expr_4072_;
goto _start;
}
case 11:
{
uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec_ref_known(v_x_4016_, 3);
v___x_4074_ = 2;
v___x_4075_ = lean_box(v___x_4074_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
default: 
{
uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec_ref(v_x_4016_);
v___x_4077_ = 0;
v___x_4078_ = lean_box(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Meta_isPropQuick(v_x_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v___x_4093_; 
lean_inc_ref(v_e_4087_);
v___x_4093_ = l_Lean_Meta_isPropQuick(v_e_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4150_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4096_ = v___x_4093_;
v_isShared_4097_ = v_isSharedCheck_4150_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4150_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
uint8_t v___x_4098_; 
v___x_4098_ = lean_unbox(v_a_4094_);
lean_dec(v_a_4094_);
switch(v___x_4098_)
{
case 0:
{
uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
lean_dec_ref(v_e_4087_);
v___x_4099_ = 0;
v___x_4100_ = lean_box(v___x_4099_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4100_);
v___x_4102_ = v___x_4096_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
case 1:
{
uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec_ref(v_e_4087_);
v___x_4104_ = 1;
v___x_4105_ = lean_box(v___x_4104_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4105_);
v___x_4107_ = v___x_4096_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
default: 
{
lean_object* v___x_4109_; 
lean_del_object(v___x_4096_);
lean_inc(v_a_4091_);
lean_inc_ref(v_a_4090_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
v___x_4109_ = lean_infer_type(v_e_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___x_4111_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4111_ = l_Lean_Meta_whnfD(v_a_4110_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4133_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4133_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4133_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
if (lean_obj_tag(v_a_4112_) == 3)
{
lean_object* v_u_4116_; lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4127_; 
lean_del_object(v___x_4114_);
v_u_4116_ = lean_ctor_get(v_a_4112_, 0);
lean_inc(v_u_4116_);
lean_dec_ref_known(v_a_4112_, 1);
v___x_4117_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4116_, v_a_4089_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4122_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4118_);
lean_dec(v_a_4118_);
v___x_4123_ = lean_box(v___x_4122_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4123_);
v___x_4125_ = v___x_4120_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
else
{
uint8_t v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
lean_dec(v_a_4112_);
v___x_4128_ = 0;
v___x_4129_ = lean_box(v___x_4128_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v___x_4129_);
v___x_4131_ = v___x_4114_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_a_4134_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4111_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4111_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
v_a_4142_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4109_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4109_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec_ref(v_e_4087_);
v_a_4151_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4093_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4093_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_Meta_isProp(v_e_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4166_){
_start:
{
switch(lean_obj_tag(v_x_4166_))
{
case 0:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_unsigned_to_nat(0u);
return v___x_4167_;
}
case 1:
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_unsigned_to_nat(1u);
return v___x_4168_;
}
case 2:
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_unsigned_to_nat(2u);
return v___x_4169_;
}
default: 
{
lean_object* v___x_4170_; 
v___x_4170_ = lean_unsigned_to_nat(3u);
return v___x_4170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4171_);
lean_dec(v_x_4171_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4173_, lean_object* v_k_4174_){
_start:
{
if (lean_obj_tag(v_t_4173_) == 3)
{
lean_object* v_idx_4175_; lean_object* v_numArgs_4176_; lean_object* v___x_4177_; 
v_idx_4175_ = lean_ctor_get(v_t_4173_, 0);
lean_inc(v_idx_4175_);
v_numArgs_4176_ = lean_ctor_get(v_t_4173_, 1);
lean_inc(v_numArgs_4176_);
lean_dec_ref_known(v_t_4173_, 2);
v___x_4177_ = lean_apply_2(v_k_4174_, v_idx_4175_, v_numArgs_4176_);
return v___x_4177_;
}
else
{
lean_dec(v_t_4173_);
return v_k_4174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4178_, lean_object* v_ctorIdx_4179_, lean_object* v_t_4180_, lean_object* v_h_4181_, lean_object* v_k_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4180_, v_k_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4184_, lean_object* v_ctorIdx_4185_, lean_object* v_t_4186_, lean_object* v_h_4187_, lean_object* v_k_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4184_, v_ctorIdx_4185_, v_t_4186_, v_h_4187_, v_k_4188_);
lean_dec(v_ctorIdx_4185_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4190_, lean_object* v_false_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4190_, v_false_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4193_, lean_object* v_t_4194_, lean_object* v_h_4195_, lean_object* v_false_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4194_, v_false_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4198_, lean_object* v_true_4199_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4198_, v_true_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4201_, lean_object* v_t_4202_, lean_object* v_h_4203_, lean_object* v_true_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4202_, v_true_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4206_, lean_object* v_undef_4207_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4206_, v_undef_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4209_, lean_object* v_t_4210_, lean_object* v_h_4211_, lean_object* v_undef_4212_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4210_, v_undef_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4214_, lean_object* v_bvar_4215_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4214_, v_bvar_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4217_, lean_object* v_t_4218_, lean_object* v_h_4219_, lean_object* v_bvar_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4218_, v_bvar_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4222_){
_start:
{
switch(v_x_4222_)
{
case 0:
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(0);
return v___x_4223_;
}
case 1:
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_box(1);
return v___x_4224_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4226_){
_start:
{
uint8_t v_x_25__boxed_4227_; lean_object* v_res_4228_; 
v_x_25__boxed_4227_ = lean_unbox(v_x_4226_);
v_res_4228_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4227_);
return v_res_4228_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4229_){
_start:
{
switch(lean_obj_tag(v_x_4229_))
{
case 0:
{
uint8_t v___x_4230_; 
v___x_4230_ = 0;
return v___x_4230_;
}
case 1:
{
uint8_t v___x_4231_; 
v___x_4231_ = 1;
return v___x_4231_;
}
default: 
{
uint8_t v___x_4232_; 
v___x_4232_ = 2;
return v___x_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4233_){
_start:
{
uint8_t v_res_4234_; lean_object* v_r_4235_; 
v_res_4234_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4233_);
lean_dec(v_x_4233_);
v_r_4235_ = lean_box(v_res_4234_);
return v_r_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4237_, lean_object* v_numArgs_4238_){
_start:
{
switch(lean_obj_tag(v_e_4237_))
{
case 3:
{
lean_object* v_u_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_u_4239_ = lean_ctor_get(v_e_4237_, 0);
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_nat_dec_eq(v_numArgs_4238_, v___x_4240_);
lean_dec(v_numArgs_4238_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
v___x_4242_ = lean_box(2);
return v___x_4242_;
}
else
{
uint8_t v___x_4243_; 
v___x_4243_ = l_Lean_Level_isNeverZero(v_u_4239_);
if (v___x_4243_ == 0)
{
uint8_t v___x_4244_; 
v___x_4244_ = l_Lean_Level_isZero(v_u_4239_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_box(2);
return v___x_4245_;
}
else
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_box(1);
return v___x_4246_;
}
}
else
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_box(0);
return v___x_4247_;
}
}
}
case 7:
{
lean_object* v_body_4248_; lean_object* v_zero_4249_; uint8_t v_isZero_4250_; 
v_body_4248_ = lean_ctor_get(v_e_4237_, 2);
v_zero_4249_ = lean_unsigned_to_nat(0u);
v_isZero_4250_ = lean_nat_dec_eq(v_numArgs_4238_, v_zero_4249_);
if (v_isZero_4250_ == 0)
{
lean_object* v_one_4251_; lean_object* v_n_4252_; 
v_one_4251_ = lean_unsigned_to_nat(1u);
v_n_4252_ = lean_nat_sub(v_numArgs_4238_, v_one_4251_);
lean_dec(v_numArgs_4238_);
v_e_4237_ = v_body_4248_;
v_numArgs_4238_ = v_n_4252_;
goto _start;
}
else
{
lean_object* v___x_4254_; 
lean_dec(v_numArgs_4238_);
v___x_4254_ = lean_box(2);
return v___x_4254_;
}
}
case 10:
{
lean_object* v_expr_4255_; 
v_expr_4255_ = lean_ctor_get(v_e_4237_, 1);
v_e_4237_ = v_expr_4255_;
goto _start;
}
case 5:
{
lean_object* v_fn_4257_; 
v_fn_4257_ = lean_ctor_get(v_e_4237_, 0);
if (lean_obj_tag(v_fn_4257_) == 4)
{
lean_object* v_declName_4258_; 
v_declName_4258_ = lean_ctor_get(v_fn_4257_, 0);
if (lean_obj_tag(v_declName_4258_) == 1)
{
lean_object* v_pre_4259_; 
v_pre_4259_ = lean_ctor_get(v_declName_4258_, 0);
if (lean_obj_tag(v_pre_4259_) == 0)
{
lean_object* v_arg_4260_; lean_object* v_str_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; 
v_arg_4260_ = lean_ctor_get(v_e_4237_, 1);
v_str_4261_ = lean_ctor_get(v_declName_4258_, 1);
v___x_4262_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4263_ = lean_string_dec_eq(v_str_4261_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
lean_dec(v_numArgs_4238_);
v___x_4264_ = lean_box(2);
return v___x_4264_;
}
else
{
v_e_4237_ = v_arg_4260_;
goto _start;
}
}
else
{
lean_object* v___x_4266_; 
lean_dec(v_numArgs_4238_);
v___x_4266_ = lean_box(2);
return v___x_4266_;
}
}
else
{
lean_object* v___x_4267_; 
lean_dec(v_numArgs_4238_);
v___x_4267_ = lean_box(2);
return v___x_4267_;
}
}
else
{
lean_object* v___x_4268_; 
lean_dec(v_numArgs_4238_);
v___x_4268_ = lean_box(2);
return v___x_4268_;
}
}
default: 
{
lean_object* v___x_4269_; 
lean_dec(v_numArgs_4238_);
v___x_4269_ = lean_box(2);
return v___x_4269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4270_, lean_object* v_numArgs_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4270_, v_numArgs_4271_);
lean_dec_ref(v_e_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4273_, lean_object* v_binderType_4274_){
_start:
{
if (lean_obj_tag(v_r_4273_) == 3)
{
lean_object* v_idx_4275_; lean_object* v_numArgs_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4288_; 
v_idx_4275_ = lean_ctor_get(v_r_4273_, 0);
v_numArgs_4276_ = lean_ctor_get(v_r_4273_, 1);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_r_4273_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4278_ = v_r_4273_;
v_isShared_4279_ = v_isSharedCheck_4288_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_numArgs_4276_);
lean_inc(v_idx_4275_);
lean_dec(v_r_4273_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4288_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_zero_4280_; uint8_t v_isZero_4281_; 
v_zero_4280_ = lean_unsigned_to_nat(0u);
v_isZero_4281_ = lean_nat_dec_eq(v_idx_4275_, v_zero_4280_);
if (v_isZero_4281_ == 1)
{
lean_object* v___x_4282_; 
lean_del_object(v___x_4278_);
lean_dec(v_idx_4275_);
v___x_4282_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4274_, v_numArgs_4276_);
return v___x_4282_;
}
else
{
lean_object* v_one_4283_; lean_object* v_n_4284_; lean_object* v___x_4286_; 
v_one_4283_ = lean_unsigned_to_nat(1u);
v_n_4284_ = lean_nat_sub(v_idx_4275_, v_one_4283_);
lean_dec(v_idx_4275_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v_n_4284_);
v___x_4286_ = v___x_4278_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_n_4284_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_numArgs_4276_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
return v_r_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4289_, lean_object* v_binderType_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4289_, v_binderType_4290_);
lean_dec_ref(v_binderType_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4292_, lean_object* v_x_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_type_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; 
switch(lean_obj_tag(v_x_4292_))
{
case 7:
{
lean_object* v_binderType_4332_; lean_object* v_body_4333_; lean_object* v_zero_4334_; uint8_t v_isZero_4335_; 
v_binderType_4332_ = lean_ctor_get(v_x_4292_, 1);
v_body_4333_ = lean_ctor_get(v_x_4292_, 2);
v_zero_4334_ = lean_unsigned_to_nat(0u);
v_isZero_4335_ = lean_nat_dec_eq(v_x_4293_, v_zero_4334_);
if (v_isZero_4335_ == 1)
{
v_type_4300_ = v_x_4292_;
v___y_4301_ = v_a_4294_;
v___y_4302_ = v_a_4295_;
v___y_4303_ = v_a_4296_;
v___y_4304_ = v_a_4297_;
goto v___jp_4299_;
}
else
{
lean_object* v_one_4336_; lean_object* v_n_4337_; lean_object* v___x_4338_; 
lean_inc_ref(v_body_4333_);
lean_inc_ref(v_binderType_4332_);
lean_dec_ref_known(v_x_4292_, 3);
v_one_4336_ = lean_unsigned_to_nat(1u);
v_n_4337_ = lean_nat_sub(v_x_4293_, v_one_4336_);
v___x_4338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4333_, v_n_4337_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_);
lean_dec(v_n_4337_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4347_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4343_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4339_, v_binderType_4332_);
lean_dec_ref(v_binderType_4332_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v___x_4343_);
v___x_4345_ = v___x_4341_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_dec_ref(v_binderType_4332_);
return v___x_4338_;
}
}
}
case 8:
{
lean_object* v_type_4348_; lean_object* v_body_4349_; lean_object* v___x_4350_; 
v_type_4348_ = lean_ctor_get(v_x_4292_, 1);
lean_inc_ref(v_type_4348_);
v_body_4349_ = lean_ctor_get(v_x_4292_, 3);
lean_inc_ref(v_body_4349_);
lean_dec_ref_known(v_x_4292_, 4);
v___x_4350_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4349_, v_x_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4359_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4351_, v_type_4348_);
lean_dec_ref(v_type_4348_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
else
{
lean_dec_ref(v_type_4348_);
return v___x_4350_;
}
}
case 10:
{
lean_object* v_expr_4360_; 
v_expr_4360_ = lean_ctor_get(v_x_4292_, 1);
lean_inc_ref(v_expr_4360_);
lean_dec_ref_known(v_x_4292_, 2);
v_x_4292_ = v_expr_4360_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v_deBruijnIndex_4362_ = lean_ctor_get(v_x_4292_, 0);
lean_inc(v_deBruijnIndex_4362_);
lean_dec_ref_known(v_x_4292_, 1);
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = lean_nat_dec_eq(v_x_4293_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_dec(v_deBruijnIndex_4362_);
goto v___jp_4329_;
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4365_, 0, v_deBruijnIndex_4362_);
lean_ctor_set(v___x_4365_, 1, v___x_4363_);
v___x_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
return v___x_4366_;
}
}
default: 
{
lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = lean_nat_dec_eq(v_x_4293_, v___x_4367_);
if (v___x_4368_ == 0)
{
lean_dec_ref(v_x_4292_);
goto v___jp_4329_;
}
else
{
v_type_4300_ = v_x_4292_;
v___y_4301_ = v_a_4294_;
v___y_4302_ = v_a_4295_;
v___y_4303_ = v_a_4296_;
v___y_4304_ = v_a_4297_;
goto v___jp_4299_;
}
}
}
v___jp_4299_:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_Expr_getAppFn(v_type_4300_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_deBruijnIndex_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_deBruijnIndex_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_deBruijnIndex_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___x_4307_ = l_Lean_Expr_getAppNumArgs(v_type_4300_);
lean_dec_ref(v_type_4300_);
v___x_4308_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4308_, 0, v_deBruijnIndex_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
return v___x_4309_;
}
else
{
lean_object* v___x_4310_; 
lean_dec_ref(v___x_4305_);
v___x_4310_ = l_Lean_Meta_isPropQuick(v_type_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4320_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4313_ = v___x_4310_;
v_isShared_4314_ = v_isSharedCheck_4320_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4310_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4320_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4315_ = lean_unbox(v_a_4311_);
lean_dec(v_a_4311_);
v___x_4316_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4315_);
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 0, v___x_4316_);
v___x_4318_ = v___x_4313_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_a_4321_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4310_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4310_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
v___jp_4329_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = lean_box(2);
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4369_, lean_object* v_x_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4369_, v_x_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_x_4370_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4377_, lean_object* v_n_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4377_, v_n_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4394_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4394_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4394_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4392_; 
v___x_4389_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4385_);
lean_dec(v_a_4385_);
v___x_4390_ = lean_box(v___x_4389_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4390_);
v___x_4392_ = v___x_4387_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
v_a_4395_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4384_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4384_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4403_, lean_object* v_n_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4403_, v_n_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec(v_n_4404_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4411_, lean_object* v_x_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
switch(lean_obj_tag(v_x_4411_))
{
case 4:
{
lean_object* v_declName_4418_; lean_object* v_us_4419_; lean_object* v___x_4420_; 
v_declName_4418_ = lean_ctor_get(v_x_4411_, 0);
lean_inc(v_declName_4418_);
v_us_4419_ = lean_ctor_get(v_x_4411_, 1);
lean_inc(v_us_4419_);
lean_dec_ref_known(v_x_4411_, 2);
v___x_4420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4418_, v_us_4419_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4421_, v_x_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
lean_dec(v_x_4412_);
return v___x_4422_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_x_4412_);
v_a_4423_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4420_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4420_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4431_; lean_object* v___x_4432_; 
v_fvarId_4431_ = lean_ctor_get(v_x_4411_, 0);
lean_inc(v_fvarId_4431_);
lean_dec_ref_known(v_x_4411_, 1);
v___x_4432_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4431_, v_a_4413_, v_a_4415_, v_a_4416_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4434_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4432_, 1);
v___x_4434_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4433_, v_x_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
lean_dec(v_x_4412_);
return v___x_4434_;
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_x_4412_);
v_a_4435_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4432_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4432_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4443_; lean_object* v___x_4444_; 
v_mvarId_4443_ = lean_ctor_get(v_x_4411_, 0);
lean_inc(v_mvarId_4443_);
lean_dec_ref_known(v_x_4411_, 1);
v___x_4444_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4443_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4446_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref_known(v___x_4444_, 1);
v___x_4446_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4445_, v_x_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
lean_dec(v_x_4412_);
return v___x_4446_;
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_x_4412_);
v_a_4447_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4444_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4444_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
case 5:
{
lean_object* v_fn_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v_fn_4455_ = lean_ctor_get(v_x_4411_, 0);
lean_inc_ref(v_fn_4455_);
lean_dec_ref_known(v_x_4411_, 2);
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_nat_add(v_x_4412_, v___x_4456_);
lean_dec(v_x_4412_);
v_x_4411_ = v_fn_4455_;
v_x_4412_ = v___x_4457_;
goto _start;
}
case 10:
{
lean_object* v_expr_4459_; 
v_expr_4459_ = lean_ctor_get(v_x_4411_, 1);
lean_inc_ref(v_expr_4459_);
lean_dec_ref_known(v_x_4411_, 2);
v_x_4411_ = v_expr_4459_;
goto _start;
}
case 8:
{
lean_object* v_body_4461_; 
v_body_4461_ = lean_ctor_get(v_x_4411_, 3);
lean_inc_ref(v_body_4461_);
lean_dec_ref_known(v_x_4411_, 4);
v_x_4411_ = v_body_4461_;
goto _start;
}
case 6:
{
lean_object* v_body_4463_; lean_object* v_zero_4464_; uint8_t v_isZero_4465_; 
v_body_4463_ = lean_ctor_get(v_x_4411_, 2);
lean_inc_ref(v_body_4463_);
lean_dec_ref_known(v_x_4411_, 3);
v_zero_4464_ = lean_unsigned_to_nat(0u);
v_isZero_4465_ = lean_nat_dec_eq(v_x_4412_, v_zero_4464_);
if (v_isZero_4465_ == 1)
{
lean_object* v___x_4466_; 
lean_dec(v_x_4412_);
v___x_4466_ = l_Lean_Meta_isProofQuick(v_body_4463_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
return v___x_4466_;
}
else
{
lean_object* v_one_4467_; lean_object* v_n_4468_; 
v_one_4467_ = lean_unsigned_to_nat(1u);
v_n_4468_ = lean_nat_sub(v_x_4412_, v_one_4467_);
lean_dec(v_x_4412_);
v_x_4411_ = v_body_4463_;
v_x_4412_ = v_n_4468_;
goto _start;
}
}
default: 
{
uint8_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec(v_x_4412_);
lean_dec_ref(v_x_4411_);
v___x_4470_ = 2;
v___x_4471_ = lean_box(v___x_4470_);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
switch(lean_obj_tag(v_x_4473_))
{
case 0:
{
uint8_t v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
lean_dec_ref_known(v_x_4473_, 1);
v___x_4479_ = 2;
v___x_4480_ = lean_box(v___x_4479_);
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
return v___x_4481_;
}
case 1:
{
lean_object* v_fvarId_4482_; lean_object* v___x_4483_; 
v_fvarId_4482_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_fvarId_4482_);
lean_dec_ref_known(v_x_4473_, 1);
v___x_4483_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4482_, v_a_4474_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4484_, v___x_4485_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4486_;
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
v_a_4487_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4483_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4483_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4495_; lean_object* v___x_4496_; 
v_mvarId_4495_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_mvarId_4495_);
lean_dec_ref_known(v_x_4473_, 1);
v___x_4496_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4495_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4497_, v___x_4498_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4499_;
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_a_4500_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4496_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4496_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
case 4:
{
lean_object* v_declName_4508_; lean_object* v_us_4509_; lean_object* v___x_4510_; 
v_declName_4508_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_declName_4508_);
v_us_4509_ = lean_ctor_get(v_x_4473_, 1);
lean_inc(v_us_4509_);
lean_dec_ref_known(v_x_4473_, 2);
v___x_4510_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4508_, v_us_4509_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4511_, v___x_4512_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4513_;
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_a_4514_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4510_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4510_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
case 5:
{
lean_object* v_fn_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_fn_4522_ = lean_ctor_get(v_x_4473_, 0);
lean_inc_ref(v_fn_4522_);
lean_dec_ref_known(v_x_4473_, 2);
v___x_4523_ = lean_unsigned_to_nat(1u);
v___x_4524_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4522_, v___x_4523_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4524_;
}
case 6:
{
lean_object* v_body_4525_; 
v_body_4525_ = lean_ctor_get(v_x_4473_, 2);
lean_inc_ref(v_body_4525_);
lean_dec_ref_known(v_x_4473_, 3);
v_x_4473_ = v_body_4525_;
goto _start;
}
case 8:
{
lean_object* v_body_4527_; 
v_body_4527_ = lean_ctor_get(v_x_4473_, 3);
lean_inc_ref(v_body_4527_);
lean_dec_ref_known(v_x_4473_, 4);
v_x_4473_ = v_body_4527_;
goto _start;
}
case 10:
{
lean_object* v_expr_4529_; 
v_expr_4529_ = lean_ctor_get(v_x_4473_, 1);
lean_inc_ref(v_expr_4529_);
lean_dec_ref_known(v_x_4473_, 2);
v_x_4473_ = v_expr_4529_;
goto _start;
}
case 11:
{
uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
lean_dec_ref_known(v_x_4473_, 3);
v___x_4531_ = 2;
v___x_4532_ = lean_box(v___x_4531_);
v___x_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
return v___x_4533_;
}
default: 
{
uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec_ref(v_x_4473_);
v___x_4534_ = 0;
v___x_4535_ = lean_box(v___x_4534_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Meta_isProofQuick(v_x_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4544_, lean_object* v_x_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4544_, v_x_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v___x_4558_; 
lean_inc_ref(v_e_4552_);
v___x_4558_ = l_Lean_Meta_isProofQuick(v_e_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4585_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4561_ = v___x_4558_;
v_isShared_4562_ = v_isSharedCheck_4585_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4585_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
uint8_t v___x_4563_; 
v___x_4563_ = lean_unbox(v_a_4559_);
lean_dec(v_a_4559_);
switch(v___x_4563_)
{
case 0:
{
uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
lean_dec_ref(v_e_4552_);
v___x_4564_ = 0;
v___x_4565_ = lean_box(v___x_4564_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4565_);
v___x_4567_ = v___x_4561_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
case 1:
{
uint8_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_dec_ref(v_e_4552_);
v___x_4569_ = 1;
v___x_4570_ = lean_box(v___x_4569_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4570_);
v___x_4572_ = v___x_4561_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
default: 
{
lean_object* v___x_4574_; 
lean_del_object(v___x_4561_);
lean_inc(v_a_4556_);
lean_inc_ref(v_a_4555_);
lean_inc(v_a_4554_);
lean_inc_ref(v_a_4553_);
v___x_4574_ = lean_infer_type(v_e_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4576_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
v___x_4576_ = l_Lean_Meta_isProp(v_a_4575_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
return v___x_4576_;
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
v_a_4577_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4574_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4574_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_dec_ref(v_e_4552_);
v_a_4586_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4558_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4558_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l_Lean_Meta_isProof(v_e_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4601_, lean_object* v_x_4602_){
_start:
{
switch(lean_obj_tag(v_x_4601_))
{
case 3:
{
lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = lean_nat_dec_eq(v_x_4602_, v___x_4608_);
lean_dec(v_x_4602_);
if (v___x_4609_ == 0)
{
goto v___jp_4604_;
}
else
{
uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = 1;
v___x_4611_ = lean_box(v___x_4610_);
v___x_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
return v___x_4612_;
}
}
case 7:
{
lean_object* v_body_4613_; lean_object* v_zero_4614_; uint8_t v_isZero_4615_; 
v_body_4613_ = lean_ctor_get(v_x_4601_, 2);
v_zero_4614_ = lean_unsigned_to_nat(0u);
v_isZero_4615_ = lean_nat_dec_eq(v_x_4602_, v_zero_4614_);
if (v_isZero_4615_ == 1)
{
uint8_t v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
lean_dec(v_x_4602_);
v___x_4616_ = 0;
v___x_4617_ = lean_box(v___x_4616_);
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
else
{
lean_object* v_one_4619_; lean_object* v_n_4620_; 
v_one_4619_ = lean_unsigned_to_nat(1u);
v_n_4620_ = lean_nat_sub(v_x_4602_, v_one_4619_);
lean_dec(v_x_4602_);
v_x_4601_ = v_body_4613_;
v_x_4602_ = v_n_4620_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4622_; 
v_body_4622_ = lean_ctor_get(v_x_4601_, 3);
v_x_4601_ = v_body_4622_;
goto _start;
}
case 10:
{
lean_object* v_expr_4624_; 
v_expr_4624_ = lean_ctor_get(v_x_4601_, 1);
v_x_4601_ = v_expr_4624_;
goto _start;
}
default: 
{
lean_dec(v_x_4602_);
goto v___jp_4604_;
}
}
v___jp_4604_:
{
uint8_t v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4605_ = 2;
v___x_4606_ = lean_box(v___x_4605_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
return v___x_4607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4626_, lean_object* v_x_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4626_, v_x_4627_);
lean_dec_ref(v_x_4626_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4630_, lean_object* v_x_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4630_, v_x_4631_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4638_, lean_object* v_x_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4638_, v_x_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec_ref(v_x_4638_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4646_, lean_object* v_x_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
switch(lean_obj_tag(v_x_4646_))
{
case 4:
{
lean_object* v_declName_4653_; lean_object* v_us_4654_; lean_object* v___x_4655_; 
v_declName_4653_ = lean_ctor_get(v_x_4646_, 0);
lean_inc(v_declName_4653_);
v_us_4654_ = lean_ctor_get(v_x_4646_, 1);
lean_inc(v_us_4654_);
lean_dec_ref_known(v_x_4646_, 2);
v___x_4655_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4653_, v_us_4654_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4657_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v___x_4657_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4656_, v_x_4647_);
lean_dec(v_a_4656_);
return v___x_4657_;
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec(v_x_4647_);
v_a_4658_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4655_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4655_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4666_; lean_object* v___x_4667_; 
v_fvarId_4666_ = lean_ctor_get(v_x_4646_, 0);
lean_inc(v_fvarId_4666_);
lean_dec_ref_known(v_x_4646_, 1);
v___x_4667_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4666_, v_a_4648_, v_a_4650_, v_a_4651_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4668_, v_x_4647_);
lean_dec(v_a_4668_);
return v___x_4669_;
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec(v_x_4647_);
v_a_4670_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4667_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4667_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4678_; lean_object* v___x_4679_; 
v_mvarId_4678_ = lean_ctor_get(v_x_4646_, 0);
lean_inc(v_mvarId_4678_);
lean_dec_ref_known(v_x_4646_, 1);
v___x_4679_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4678_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref_known(v___x_4679_, 1);
v___x_4681_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4680_, v_x_4647_);
lean_dec(v_a_4680_);
return v___x_4681_;
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec(v_x_4647_);
v_a_4682_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4679_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4679_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
case 5:
{
lean_object* v_fn_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_fn_4690_ = lean_ctor_get(v_x_4646_, 0);
lean_inc_ref(v_fn_4690_);
lean_dec_ref_known(v_x_4646_, 2);
v___x_4691_ = lean_unsigned_to_nat(1u);
v___x_4692_ = lean_nat_add(v_x_4647_, v___x_4691_);
lean_dec(v_x_4647_);
v_x_4646_ = v_fn_4690_;
v_x_4647_ = v___x_4692_;
goto _start;
}
case 10:
{
lean_object* v_expr_4694_; 
v_expr_4694_ = lean_ctor_get(v_x_4646_, 1);
lean_inc_ref(v_expr_4694_);
lean_dec_ref_known(v_x_4646_, 2);
v_x_4646_ = v_expr_4694_;
goto _start;
}
case 8:
{
lean_object* v_body_4696_; 
v_body_4696_ = lean_ctor_get(v_x_4646_, 3);
lean_inc_ref(v_body_4696_);
lean_dec_ref_known(v_x_4646_, 4);
v_x_4646_ = v_body_4696_;
goto _start;
}
case 6:
{
lean_object* v_body_4698_; lean_object* v_zero_4699_; uint8_t v_isZero_4700_; 
v_body_4698_ = lean_ctor_get(v_x_4646_, 2);
lean_inc_ref(v_body_4698_);
lean_dec_ref_known(v_x_4646_, 3);
v_zero_4699_ = lean_unsigned_to_nat(0u);
v_isZero_4700_ = lean_nat_dec_eq(v_x_4647_, v_zero_4699_);
if (v_isZero_4700_ == 1)
{
uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
lean_dec_ref(v_body_4698_);
lean_dec(v_x_4647_);
v___x_4701_ = 0;
v___x_4702_ = lean_box(v___x_4701_);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
return v___x_4703_;
}
else
{
lean_object* v_one_4704_; lean_object* v_n_4705_; 
v_one_4704_ = lean_unsigned_to_nat(1u);
v_n_4705_ = lean_nat_sub(v_x_4647_, v_one_4704_);
lean_dec(v_x_4647_);
v_x_4646_ = v_body_4698_;
v_x_4647_ = v_n_4705_;
goto _start;
}
}
default: 
{
uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_dec(v_x_4647_);
lean_dec_ref(v_x_4646_);
v___x_4707_ = 2;
v___x_4708_ = lean_box(v___x_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4710_, lean_object* v_x_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4710_, v_x_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
switch(lean_obj_tag(v_x_4718_))
{
case 1:
{
lean_object* v_fvarId_4724_; lean_object* v___x_4725_; 
v_fvarId_4724_ = lean_ctor_get(v_x_4718_, 0);
lean_inc(v_fvarId_4724_);
lean_dec_ref_known(v_x_4718_, 1);
v___x_4725_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4724_, v_a_4719_, v_a_4721_, v_a_4722_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
lean_inc(v_a_4726_);
lean_dec_ref_known(v___x_4725_, 1);
v___x_4727_ = lean_unsigned_to_nat(0u);
v___x_4728_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4726_, v___x_4727_);
lean_dec(v_a_4726_);
return v___x_4728_;
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
v_a_4729_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4725_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4725_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4737_; lean_object* v___x_4738_; 
v_mvarId_4737_ = lean_ctor_get(v_x_4718_, 0);
lean_inc(v_mvarId_4737_);
lean_dec_ref_known(v_x_4718_, 1);
v___x_4738_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4737_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4738_, 1);
v___x_4740_ = lean_unsigned_to_nat(0u);
v___x_4741_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4739_, v___x_4740_);
lean_dec(v_a_4739_);
return v___x_4741_;
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
v_a_4742_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4738_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4738_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
case 3:
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_dec_ref_known(v_x_4718_, 1);
v___x_4750_ = 1;
v___x_4751_ = lean_box(v___x_4750_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
case 4:
{
lean_object* v_declName_4753_; lean_object* v_us_4754_; lean_object* v___x_4755_; 
v_declName_4753_ = lean_ctor_get(v_x_4718_, 0);
lean_inc(v_declName_4753_);
v_us_4754_ = lean_ctor_get(v_x_4718_, 1);
lean_inc(v_us_4754_);
lean_dec_ref_known(v_x_4718_, 2);
v___x_4755_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4753_, v_us_4754_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4755_, 1);
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4756_, v___x_4757_);
lean_dec(v_a_4756_);
return v___x_4758_;
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
v_a_4759_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4755_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4755_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
case 5:
{
lean_object* v_fn_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v_fn_4767_ = lean_ctor_get(v_x_4718_, 0);
lean_inc_ref(v_fn_4767_);
lean_dec_ref_known(v_x_4718_, 2);
v___x_4768_ = lean_unsigned_to_nat(1u);
v___x_4769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4767_, v___x_4768_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4769_;
}
case 6:
{
uint8_t v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec_ref_known(v_x_4718_, 3);
v___x_4770_ = 0;
v___x_4771_ = lean_box(v___x_4770_);
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
case 7:
{
uint8_t v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
lean_dec_ref_known(v_x_4718_, 3);
v___x_4773_ = 1;
v___x_4774_ = lean_box(v___x_4773_);
v___x_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
return v___x_4775_;
}
case 8:
{
lean_object* v_body_4776_; 
v_body_4776_ = lean_ctor_get(v_x_4718_, 3);
lean_inc_ref(v_body_4776_);
lean_dec_ref_known(v_x_4718_, 4);
v_x_4718_ = v_body_4776_;
goto _start;
}
case 9:
{
uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
lean_dec_ref_known(v_x_4718_, 1);
v___x_4778_ = 0;
v___x_4779_ = lean_box(v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
case 10:
{
lean_object* v_expr_4781_; 
v_expr_4781_ = lean_ctor_get(v_x_4718_, 1);
lean_inc_ref(v_expr_4781_);
lean_dec_ref_known(v_x_4718_, 2);
v_x_4718_ = v_expr_4781_;
goto _start;
}
default: 
{
uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
lean_dec_ref(v_x_4718_);
v___x_4783_ = 2;
v___x_4784_ = lean_box(v___x_4783_);
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Lean_Meta_isTypeQuick(v_x_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
lean_dec(v_a_4790_);
lean_dec_ref(v_a_4789_);
lean_dec(v_a_4788_);
lean_dec_ref(v_a_4787_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v___x_4799_; 
lean_inc_ref(v_e_4793_);
v___x_4799_ = l_Lean_Meta_isTypeQuick(v_e_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4849_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4849_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4849_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
uint8_t v___x_4804_; 
v___x_4804_ = lean_unbox(v_a_4800_);
lean_dec(v_a_4800_);
switch(v___x_4804_)
{
case 0:
{
uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_dec_ref(v_e_4793_);
v___x_4805_ = 0;
v___x_4806_ = lean_box(v___x_4805_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4806_);
v___x_4808_ = v___x_4802_;
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
case 1:
{
uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
lean_dec_ref(v_e_4793_);
v___x_4810_ = 1;
v___x_4811_ = lean_box(v___x_4810_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4811_);
v___x_4813_ = v___x_4802_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
default: 
{
lean_object* v___x_4815_; 
lean_del_object(v___x_4802_);
lean_inc(v_a_4797_);
lean_inc_ref(v_a_4796_);
lean_inc(v_a_4795_);
lean_inc_ref(v_a_4794_);
v___x_4815_ = lean_infer_type(v_e_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4817_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
lean_dec_ref_known(v___x_4815_, 1);
v___x_4817_ = l_Lean_Meta_whnfD(v_a_4816_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4832_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4832_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4832_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
if (lean_obj_tag(v_a_4818_) == 3)
{
uint8_t v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4825_; 
lean_dec_ref_known(v_a_4818_, 1);
v___x_4822_ = 1;
v___x_4823_ = lean_box(v___x_4822_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4823_);
v___x_4825_ = v___x_4820_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
else
{
uint8_t v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_dec(v_a_4818_);
v___x_4827_ = 0;
v___x_4828_ = lean_box(v___x_4827_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4828_);
v___x_4830_ = v___x_4820_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4833_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4817_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4817_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
v_a_4841_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4815_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4815_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec_ref(v_e_4793_);
v_a_4850_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4799_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4799_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Meta_isType(v_e_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4865_){
_start:
{
switch(lean_obj_tag(v_x_4865_))
{
case 7:
{
lean_object* v_body_4866_; 
v_body_4866_ = lean_ctor_get(v_x_4865_, 2);
v_x_4865_ = v_body_4866_;
goto _start;
}
case 3:
{
lean_object* v_u_4868_; lean_object* v___x_4869_; 
v_u_4868_ = lean_ctor_get(v_x_4865_, 0);
lean_inc(v_u_4868_);
v___x_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4869_, 0, v_u_4868_);
return v___x_4869_;
}
default: 
{
lean_object* v___x_4870_; 
v___x_4870_ = lean_box(0);
return v___x_4870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4871_);
lean_dec_ref(v_x_4871_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4873_, lean_object* v_body_4874_, lean_object* v_x_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4873_, v_body_4874_, v_x_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4884_, lean_object* v_xs_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_){
_start:
{
switch(lean_obj_tag(v_type_4884_))
{
case 3:
{
lean_object* v_u_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref(v_xs_4885_);
v_u_4891_ = lean_ctor_get(v_type_4884_, 0);
lean_inc(v_u_4891_);
lean_dec_ref_known(v_type_4884_, 1);
v___x_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_u_4891_);
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
return v___x_4893_;
}
case 7:
{
lean_object* v_binderName_4894_; lean_object* v_binderType_4895_; lean_object* v_body_4896_; uint8_t v_binderInfo_4897_; lean_object* v___f_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v_binderName_4894_ = lean_ctor_get(v_type_4884_, 0);
lean_inc(v_binderName_4894_);
v_binderType_4895_ = lean_ctor_get(v_type_4884_, 1);
lean_inc_ref(v_binderType_4895_);
v_body_4896_ = lean_ctor_get(v_type_4884_, 2);
lean_inc_ref(v_body_4896_);
v_binderInfo_4897_ = lean_ctor_get_uint8(v_type_4884_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4884_, 3);
lean_inc_ref(v_xs_4885_);
v___f_4898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4898_, 0, v_xs_4885_);
lean_closure_set(v___f_4898_, 1, v_body_4896_);
v___x_4899_ = lean_expr_instantiate_rev(v_binderType_4895_, v_xs_4885_);
lean_dec_ref(v_xs_4885_);
lean_dec_ref(v_binderType_4895_);
v___x_4900_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4894_, v_binderInfo_4897_, v___x_4899_, v___f_4898_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_);
return v___x_4900_;
}
default: 
{
lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4901_ = lean_expr_instantiate_rev(v_type_4884_, v_xs_4885_);
lean_dec_ref(v_xs_4885_);
lean_dec_ref(v_type_4884_);
v___x_4902_ = l_Lean_Meta_whnfD(v___x_4901_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4918_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4905_ = v___x_4902_;
v_isShared_4906_ = v_isSharedCheck_4918_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4918_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
switch(lean_obj_tag(v_a_4903_))
{
case 3:
{
lean_object* v_u_4907_; lean_object* v___x_4908_; lean_object* v___x_4910_; 
v_u_4907_ = lean_ctor_get(v_a_4903_, 0);
lean_inc(v_u_4907_);
lean_dec_ref_known(v_a_4903_, 1);
v___x_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4908_, 0, v_u_4907_);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v___x_4908_);
v___x_4910_ = v___x_4905_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
case 7:
{
lean_object* v___x_4912_; 
lean_del_object(v___x_4905_);
v___x_4912_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4884_ = v_a_4903_;
v_xs_4885_ = v___x_4912_;
goto _start;
}
default: 
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
lean_dec(v_a_4903_);
v___x_4914_ = lean_box(0);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v___x_4914_);
v___x_4916_ = v___x_4905_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
v_a_4919_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4902_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4902_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4927_, lean_object* v_body_4928_, lean_object* v_x_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = lean_array_push(v_xs_4927_, v_x_4929_);
v___x_4936_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4928_, v___x_4935_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4937_, lean_object* v_xs_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4937_, v_xs_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4945_, lean_object* v_cache_4946_, lean_object* v_a_x3f_4947_){
_start:
{
lean_object* v___x_4949_; lean_object* v_mctx_4950_; lean_object* v_zetaDeltaFVarIds_4951_; lean_object* v_postponed_4952_; lean_object* v_diag_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4963_; 
v___x_4949_ = lean_st_ref_take(v_a_4945_);
v_mctx_4950_ = lean_ctor_get(v___x_4949_, 0);
v_zetaDeltaFVarIds_4951_ = lean_ctor_get(v___x_4949_, 2);
v_postponed_4952_ = lean_ctor_get(v___x_4949_, 3);
v_diag_4953_ = lean_ctor_get(v___x_4949_, 4);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4963_ == 0)
{
lean_object* v_unused_4964_; 
v_unused_4964_ = lean_ctor_get(v___x_4949_, 1);
lean_dec(v_unused_4964_);
v___x_4955_ = v___x_4949_;
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_diag_4953_);
lean_inc(v_postponed_4952_);
lean_inc(v_zetaDeltaFVarIds_4951_);
lean_inc(v_mctx_4950_);
lean_dec(v___x_4949_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4957_; lean_object* v___x_4959_; 
v___x_4957_ = lean_box(0);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v_cache_4946_);
v___x_4959_ = v___x_4955_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_mctx_4950_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_cache_4946_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_zetaDeltaFVarIds_4951_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_postponed_4952_);
lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_diag_4953_);
v___x_4959_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = lean_st_ref_put(v_a_4945_, v___x_4959_);
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4957_);
return v___x_4961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4965_, lean_object* v_cache_4966_, lean_object* v_a_x3f_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4965_, v_cache_4966_, v_a_x3f_4967_);
lean_dec(v_a_x3f_4967_);
lean_dec(v_a_4965_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v___x_4976_; 
v___x_4976_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4970_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v_cache_4979_; lean_object* v___x_4980_; 
v___x_4977_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4978_ = lean_st_ref_get(v_a_4972_);
v_cache_4979_ = lean_ctor_get(v___x_4978_, 1);
lean_inc_ref(v_cache_4979_);
lean_dec(v___x_4978_);
v___x_4980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4970_, v___x_4977_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4997_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4983_ = v___x_4980_;
v_isShared_4984_ = v_isSharedCheck_4997_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4997_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
lean_inc(v_a_4981_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set_tag(v___x_4983_, 1);
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
v___x_4987_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4972_, v_cache_4979_, v___x_4986_);
lean_dec_ref(v___x_4986_);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_4994_ == 0)
{
lean_object* v_unused_4995_; 
v_unused_4995_ = lean_ctor_get(v___x_4987_, 0);
lean_dec(v_unused_4995_);
v___x_4989_ = v___x_4987_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_dec(v___x_4987_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v_a_4981_);
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4981_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
v_a_4998_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4998_);
lean_dec_ref_known(v___x_4980_, 1);
v___x_4999_ = lean_box(0);
v___x_5000_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4972_, v_cache_4979_, v___x_4999_);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5007_ == 0)
{
lean_object* v_unused_5008_; 
v_unused_5008_ = lean_ctor_get(v___x_5000_, 0);
lean_dec(v_unused_5008_);
v___x_5002_ = v___x_5000_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_dec(v___x_5000_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 1);
lean_ctor_set(v___x_5002_, 0, v_a_4998_);
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_4998_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
else
{
lean_object* v___x_5009_; 
lean_dec_ref(v_type_4970_);
v___x_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5009_, 0, v___x_4976_);
return v___x_5009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
lean_dec(v_a_5014_);
lean_dec_ref(v_a_5013_);
lean_dec(v_a_5012_);
lean_dec_ref(v_a_5011_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5038_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5026_ = v___x_5023_;
v_isShared_5027_ = v_isSharedCheck_5038_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5038_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
if (lean_obj_tag(v_a_5024_) == 0)
{
uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5028_ = 0;
v___x_5029_ = lean_box(v___x_5028_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5029_);
v___x_5031_ = v___x_5026_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
else
{
uint8_t v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
lean_dec_ref_known(v_a_5024_, 1);
v___x_5033_ = 1;
v___x_5034_ = lean_box(v___x_5033_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5034_);
v___x_5036_ = v___x_5026_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
v_a_5039_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5023_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5023_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_Meta_isTypeFormerType(v_type_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
return v_res_5053_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5054_, lean_object* v_x_5055_){
_start:
{
if (lean_obj_tag(v_x_5054_) == 0)
{
if (lean_obj_tag(v_x_5055_) == 0)
{
uint8_t v___x_5056_; 
v___x_5056_ = 1;
return v___x_5056_;
}
else
{
uint8_t v___x_5057_; 
v___x_5057_ = 0;
return v___x_5057_;
}
}
else
{
if (lean_obj_tag(v_x_5055_) == 0)
{
uint8_t v___x_5058_; 
v___x_5058_ = 0;
return v___x_5058_;
}
else
{
lean_object* v_val_5059_; lean_object* v_val_5060_; uint8_t v___x_5061_; 
v_val_5059_ = lean_ctor_get(v_x_5054_, 0);
v_val_5060_ = lean_ctor_get(v_x_5055_, 0);
v___x_5061_ = lean_level_eq(v_val_5059_, v_val_5060_);
return v___x_5061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
uint8_t v_res_5064_; lean_object* v_r_5065_; 
v_res_5064_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5062_, v_x_5063_);
lean_dec(v_x_5063_);
lean_dec(v_x_5062_);
v_r_5065_ = lean_box(v_res_5064_);
return v_r_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5085_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5077_ = v___x_5074_;
v_isShared_5078_ = v_isSharedCheck_5085_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5074_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5085_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___x_5079_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5080_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5075_, v___x_5079_);
lean_dec(v_a_5075_);
v___x_5081_ = lean_box(v___x_5080_);
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 0, v___x_5081_);
v___x_5083_ = v___x_5077_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v_a_5086_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5074_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5074_);
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
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l_Lean_Meta_isPropFormerType(v_type_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5095_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v___x_5107_; 
lean_inc(v_a_5105_);
lean_inc_ref(v_a_5104_);
lean_inc(v_a_5103_);
lean_inc_ref(v_a_5102_);
v___x_5107_ = lean_infer_type(v_e_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5109_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5107_, 1);
v___x_5109_ = l_Lean_Meta_isTypeFormerType(v_a_5108_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_);
return v___x_5109_;
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
v_a_5110_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5107_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5107_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_isTypeFormer(v_e_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5125_, lean_object* v_maxFVars_x3f_5126_, lean_object* v_k_5127_, uint8_t v_cleanupAnnotations_5128_, uint8_t v_whnfType_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v___f_5135_; lean_object* v___x_5136_; 
v___f_5135_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5135_, 0, v_k_5127_);
v___x_5136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5125_, v_maxFVars_x3f_5126_, v___f_5135_, v_cleanupAnnotations_5128_, v_whnfType_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5136_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5136_);
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
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
v_a_5145_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5136_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5136_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5153_, lean_object* v_maxFVars_x3f_5154_, lean_object* v_k_5155_, lean_object* v_cleanupAnnotations_5156_, lean_object* v_whnfType_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5163_; uint8_t v_whnfType_boxed_5164_; lean_object* v_res_5165_; 
v_cleanupAnnotations_boxed_5163_ = lean_unbox(v_cleanupAnnotations_5156_);
v_whnfType_boxed_5164_ = lean_unbox(v_whnfType_5157_);
v_res_5165_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5153_, v_maxFVars_x3f_5154_, v_k_5155_, v_cleanupAnnotations_boxed_5163_, v_whnfType_boxed_5164_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5166_, lean_object* v_type_5167_, lean_object* v_maxFVars_x3f_5168_, lean_object* v_k_5169_, uint8_t v_cleanupAnnotations_5170_, uint8_t v_whnfType_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5167_, v_maxFVars_x3f_5168_, v_k_5169_, v_cleanupAnnotations_5170_, v_whnfType_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5178_, lean_object* v_type_5179_, lean_object* v_maxFVars_x3f_5180_, lean_object* v_k_5181_, lean_object* v_cleanupAnnotations_5182_, lean_object* v_whnfType_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5189_; uint8_t v_whnfType_boxed_5190_; lean_object* v_res_5191_; 
v_cleanupAnnotations_boxed_5189_ = lean_unbox(v_cleanupAnnotations_5182_);
v_whnfType_boxed_5190_ = lean_unbox(v_whnfType_5183_);
v_res_5191_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5178_, v_type_5179_, v_maxFVars_x3f_5180_, v_k_5181_, v_cleanupAnnotations_boxed_5189_, v_whnfType_boxed_5190_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
return v_res_5191_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5192_, lean_object* v_as_5193_, size_t v_i_5194_, size_t v_stop_5195_){
_start:
{
uint8_t v___x_5196_; 
v___x_5196_ = lean_usize_dec_eq(v_i_5194_, v_stop_5195_);
if (v___x_5196_ == 0)
{
lean_object* v___x_5197_; uint8_t v___x_5198_; 
v___x_5197_ = lean_array_uget_borrowed(v_as_5193_, v_i_5194_);
v___x_5198_ = lean_expr_eqv(v_a_5192_, v___x_5197_);
if (v___x_5198_ == 0)
{
size_t v___x_5199_; size_t v___x_5200_; 
v___x_5199_ = ((size_t)1ULL);
v___x_5200_ = lean_usize_add(v_i_5194_, v___x_5199_);
v_i_5194_ = v___x_5200_;
goto _start;
}
else
{
return v___x_5198_;
}
}
else
{
uint8_t v___x_5202_; 
v___x_5202_ = 0;
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5203_, lean_object* v_as_5204_, lean_object* v_i_5205_, lean_object* v_stop_5206_){
_start:
{
size_t v_i_boxed_5207_; size_t v_stop_boxed_5208_; uint8_t v_res_5209_; lean_object* v_r_5210_; 
v_i_boxed_5207_ = lean_unbox_usize(v_i_5205_);
lean_dec(v_i_5205_);
v_stop_boxed_5208_ = lean_unbox_usize(v_stop_5206_);
lean_dec(v_stop_5206_);
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5203_, v_as_5204_, v_i_boxed_5207_, v_stop_boxed_5208_);
lean_dec_ref(v_as_5204_);
lean_dec_ref(v_a_5203_);
v_r_5210_ = lean_box(v_res_5209_);
return v_r_5210_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_array_get_size(v_as_5211_);
v___x_5215_ = lean_nat_dec_lt(v___x_5213_, v___x_5214_);
if (v___x_5215_ == 0)
{
return v___x_5215_;
}
else
{
if (v___x_5215_ == 0)
{
return v___x_5215_;
}
else
{
size_t v___x_5216_; size_t v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = ((size_t)0ULL);
v___x_5217_ = lean_usize_of_nat(v___x_5214_);
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5212_, v_as_5211_, v___x_5216_, v___x_5217_);
return v___x_5218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5219_, lean_object* v_a_5220_){
_start:
{
uint8_t v_res_5221_; lean_object* v_r_5222_; 
v_res_5221_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5219_, v_a_5220_);
lean_dec_ref(v_a_5220_);
lean_dec_ref(v_as_5219_);
v_r_5222_ = lean_box(v_res_5221_);
return v_r_5222_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5223_, lean_object* v_e_5224_){
_start:
{
uint8_t v___x_5225_; lean_object* v_d_5227_; lean_object* v_b_5228_; 
v___x_5225_ = l_Lean_Expr_hasFVar(v_e_5224_);
if (v___x_5225_ == 0)
{
lean_dec_ref(v_e_5224_);
return v___x_5225_;
}
else
{
switch(lean_obj_tag(v_e_5224_))
{
case 7:
{
lean_object* v_binderType_5231_; lean_object* v_body_5232_; 
v_binderType_5231_ = lean_ctor_get(v_e_5224_, 1);
lean_inc_ref(v_binderType_5231_);
v_body_5232_ = lean_ctor_get(v_e_5224_, 2);
lean_inc_ref(v_body_5232_);
lean_dec_ref_known(v_e_5224_, 3);
v_d_5227_ = v_binderType_5231_;
v_b_5228_ = v_body_5232_;
goto v___jp_5226_;
}
case 6:
{
lean_object* v_binderType_5233_; lean_object* v_body_5234_; 
v_binderType_5233_ = lean_ctor_get(v_e_5224_, 1);
lean_inc_ref(v_binderType_5233_);
v_body_5234_ = lean_ctor_get(v_e_5224_, 2);
lean_inc_ref(v_body_5234_);
lean_dec_ref_known(v_e_5224_, 3);
v_d_5227_ = v_binderType_5233_;
v_b_5228_ = v_body_5234_;
goto v___jp_5226_;
}
case 10:
{
lean_object* v_expr_5235_; 
v_expr_5235_ = lean_ctor_get(v_e_5224_, 1);
lean_inc_ref(v_expr_5235_);
lean_dec_ref_known(v_e_5224_, 2);
v_e_5224_ = v_expr_5235_;
goto _start;
}
case 8:
{
lean_object* v_type_5237_; lean_object* v_value_5238_; lean_object* v_body_5239_; uint8_t v___x_5240_; 
v_type_5237_ = lean_ctor_get(v_e_5224_, 1);
lean_inc_ref(v_type_5237_);
v_value_5238_ = lean_ctor_get(v_e_5224_, 2);
lean_inc_ref(v_value_5238_);
v_body_5239_ = lean_ctor_get(v_e_5224_, 3);
lean_inc_ref(v_body_5239_);
lean_dec_ref_known(v_e_5224_, 4);
v___x_5240_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5223_, v_type_5237_);
if (v___x_5240_ == 0)
{
uint8_t v___x_5241_; 
v___x_5241_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5223_, v_value_5238_);
if (v___x_5241_ == 0)
{
v_e_5224_ = v_body_5239_;
goto _start;
}
else
{
lean_dec_ref(v_body_5239_);
return v___x_5225_;
}
}
else
{
lean_dec_ref(v_body_5239_);
lean_dec_ref(v_value_5238_);
return v___x_5225_;
}
}
case 5:
{
lean_object* v_fn_5243_; lean_object* v_arg_5244_; uint8_t v___x_5245_; 
v_fn_5243_ = lean_ctor_get(v_e_5224_, 0);
lean_inc_ref(v_fn_5243_);
v_arg_5244_ = lean_ctor_get(v_e_5224_, 1);
lean_inc_ref(v_arg_5244_);
lean_dec_ref_known(v_e_5224_, 2);
v___x_5245_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5223_, v_fn_5243_);
if (v___x_5245_ == 0)
{
v_e_5224_ = v_arg_5244_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5244_);
return v___x_5225_;
}
}
case 11:
{
lean_object* v_struct_5247_; 
v_struct_5247_ = lean_ctor_get(v_e_5224_, 2);
lean_inc_ref(v_struct_5247_);
lean_dec_ref_known(v_e_5224_, 3);
v_e_5224_ = v_struct_5247_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5249_; lean_object* v___x_5250_; uint8_t v___x_5251_; 
v_fvarId_5249_ = lean_ctor_get(v_e_5224_, 0);
lean_inc(v_fvarId_5249_);
lean_dec_ref_known(v_e_5224_, 1);
v___x_5250_ = l_Lean_Expr_fvar___override(v_fvarId_5249_);
v___x_5251_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5223_, v___x_5250_);
lean_dec_ref(v___x_5250_);
return v___x_5251_;
}
default: 
{
uint8_t v___x_5252_; 
lean_dec_ref(v_e_5224_);
v___x_5252_ = 0;
return v___x_5252_;
}
}
}
v___jp_5226_:
{
uint8_t v___x_5229_; 
v___x_5229_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5223_, v_d_5227_);
if (v___x_5229_ == 0)
{
v_e_5224_ = v_b_5228_;
goto _start;
}
else
{
lean_dec_ref(v_b_5228_);
return v___x_5225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5253_, lean_object* v_e_5254_){
_start:
{
uint8_t v_res_5255_; lean_object* v_r_5256_; 
v_res_5255_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5253_, v_e_5254_);
lean_dec_ref(v_xs_5253_);
v_r_5256_ = lean_box(v_res_5255_);
return v_r_5256_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; 
v___x_5258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5259_ = l_Lean_stringToMessageData(v___x_5258_);
return v___x_5259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5262_ = l_Lean_stringToMessageData(v___x_5261_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5263_, lean_object* v_type_5264_, lean_object* v_as_5265_, size_t v_sz_5266_, size_t v_i_5267_, lean_object* v_b_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v_a_5275_; uint8_t v___x_5279_; 
v___x_5279_ = lean_usize_dec_lt(v_i_5267_, v_sz_5266_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5280_; 
lean_dec_ref(v_type_5264_);
v___x_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5280_, 0, v_b_5268_);
return v___x_5280_;
}
else
{
lean_object* v___x_5281_; lean_object* v_a_5282_; uint8_t v___x_5283_; 
v___x_5281_ = lean_box(0);
v_a_5282_ = lean_array_uget_borrowed(v_as_5265_, v_i_5267_);
lean_inc(v_a_5282_);
v___x_5283_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5263_, v_a_5282_);
if (v___x_5283_ == 0)
{
v_a_5275_ = v___x_5281_;
goto v___jp_5274_;
}
else
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5284_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5282_);
v___x_5285_ = l_Lean_MessageData_ofExpr(v_a_5282_);
v___x_5286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5284_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
v___x_5287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5286_);
lean_ctor_set(v___x_5288_, 1, v___x_5287_);
lean_inc_ref(v_type_5264_);
v___x_5289_ = l_Lean_MessageData_ofExpr(v_type_5264_);
v___x_5290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5288_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
v___x_5291_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5290_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_dec_ref_known(v___x_5291_, 1);
v_a_5275_ = v___x_5281_;
goto v___jp_5274_;
}
else
{
lean_dec_ref(v_type_5264_);
return v___x_5291_;
}
}
}
v___jp_5274_:
{
size_t v___x_5276_; size_t v___x_5277_; 
v___x_5276_ = ((size_t)1ULL);
v___x_5277_ = lean_usize_add(v_i_5267_, v___x_5276_);
v_i_5267_ = v___x_5277_;
v_b_5268_ = v_a_5275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5292_, lean_object* v_type_5293_, lean_object* v_as_5294_, lean_object* v_sz_5295_, lean_object* v_i_5296_, lean_object* v_b_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
size_t v_sz_boxed_5303_; size_t v_i_boxed_5304_; lean_object* v_res_5305_; 
v_sz_boxed_5303_ = lean_unbox_usize(v_sz_5295_);
lean_dec(v_sz_5295_);
v_i_boxed_5304_ = lean_unbox_usize(v_i_5296_);
lean_dec(v_i_5296_);
v_res_5305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5292_, v_type_5293_, v_as_5294_, v_sz_boxed_5303_, v_i_boxed_5304_, v_b_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec_ref(v_as_5294_);
lean_dec_ref(v_xs_5292_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5306_, size_t v_i_5307_, lean_object* v_bs_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
uint8_t v___x_5314_; 
v___x_5314_ = lean_usize_dec_lt(v_i_5307_, v_sz_5306_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; 
v___x_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5315_, 0, v_bs_5308_);
return v___x_5315_;
}
else
{
lean_object* v_v_5316_; lean_object* v___x_5317_; lean_object* v_bs_x27_5318_; lean_object* v___x_5319_; 
v_v_5316_ = lean_array_uget(v_bs_5308_, v_i_5307_);
v___x_5317_ = lean_unsigned_to_nat(0u);
v_bs_x27_5318_ = lean_array_uset(v_bs_5308_, v_i_5307_, v___x_5317_);
lean_inc(v___y_5312_);
lean_inc_ref(v___y_5311_);
lean_inc(v___y_5310_);
lean_inc_ref(v___y_5309_);
v___x_5319_ = lean_infer_type(v_v_5316_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_object* v_a_5320_; size_t v___x_5321_; size_t v___x_5322_; lean_object* v___x_5323_; 
v_a_5320_ = lean_ctor_get(v___x_5319_, 0);
lean_inc(v_a_5320_);
lean_dec_ref_known(v___x_5319_, 1);
v___x_5321_ = ((size_t)1ULL);
v___x_5322_ = lean_usize_add(v_i_5307_, v___x_5321_);
v___x_5323_ = lean_array_uset(v_bs_x27_5318_, v_i_5307_, v_a_5320_);
v_i_5307_ = v___x_5322_;
v_bs_5308_ = v___x_5323_;
goto _start;
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec_ref(v_bs_x27_5318_);
v_a_5325_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5319_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5319_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5333_, lean_object* v_i_5334_, lean_object* v_bs_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
size_t v_sz_boxed_5341_; size_t v_i_boxed_5342_; lean_object* v_res_5343_; 
v_sz_boxed_5341_ = lean_unbox_usize(v_sz_5333_);
lean_dec(v_sz_5333_);
v_i_boxed_5342_ = lean_unbox_usize(v_i_5334_);
lean_dec(v_i_5334_);
v_res_5343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5341_, v_i_boxed_5342_, v_bs_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
return v_res_5343_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5345_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5346_ = l_Lean_stringToMessageData(v___x_5345_);
return v___x_5346_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5349_ = l_Lean_stringToMessageData(v___x_5348_);
return v___x_5349_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5351_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5352_ = l_Lean_stringToMessageData(v___x_5351_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5353_, lean_object* v_n_5354_, lean_object* v_xs_5355_, lean_object* v_x_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v___x_5386_; uint8_t v___x_5387_; 
v___x_5386_ = lean_array_get_size(v_xs_5355_);
v___x_5387_ = lean_nat_dec_eq(v___x_5386_, v_n_5354_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec_ref(v_xs_5355_);
v___x_5388_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5389_ = l_Lean_MessageData_ofExpr(v_type_5353_);
v___x_5390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5388_);
lean_ctor_set(v___x_5390_, 1, v___x_5389_);
v___x_5391_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5390_);
lean_ctor_set(v___x_5392_, 1, v___x_5391_);
v___x_5393_ = l_Nat_reprFast(v_n_5354_);
v___x_5394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5394_, 0, v___x_5393_);
v___x_5395_ = l_Lean_MessageData_ofFormat(v___x_5394_);
v___x_5396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5392_);
lean_ctor_set(v___x_5396_, 1, v___x_5395_);
v___x_5397_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5396_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5398_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5399_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5399_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
else
{
lean_dec(v_n_5354_);
goto v___jp_5362_;
}
v___jp_5362_:
{
size_t v_sz_5363_; size_t v___x_5364_; lean_object* v___x_5365_; 
v_sz_5363_ = lean_array_size(v_xs_5355_);
v___x_5364_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5355_);
v___x_5365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5363_, v___x_5364_, v_xs_5355_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v___x_5367_; size_t v_sz_5368_; lean_object* v___x_5369_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5366_);
lean_dec_ref_known(v___x_5365_, 1);
v___x_5367_ = lean_box(0);
v_sz_5368_ = lean_array_size(v_a_5366_);
v___x_5369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5355_, v_type_5353_, v_a_5366_, v_sz_5368_, v___x_5364_, v___x_5367_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
lean_dec_ref(v_xs_5355_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5376_ == 0)
{
lean_object* v_unused_5377_; 
v_unused_5377_ = lean_ctor_get(v___x_5369_, 0);
lean_dec(v_unused_5377_);
v___x_5371_ = v___x_5369_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_dec(v___x_5369_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 0, v_a_5366_);
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5366_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
else
{
lean_object* v_a_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5385_; 
lean_dec(v_a_5366_);
v_a_5378_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5380_ = v___x_5369_;
v_isShared_5381_ = v_isSharedCheck_5385_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_a_5378_);
lean_dec(v___x_5369_);
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
}
else
{
lean_dec_ref(v_xs_5355_);
lean_dec_ref(v_type_5353_);
return v___x_5365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5408_, lean_object* v_n_5409_, lean_object* v_xs_5410_, lean_object* v_x_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5408_, v_n_5409_, v_xs_5410_, v_x_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v___y_5412_);
lean_dec_ref(v_x_5411_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5418_, lean_object* v_type_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v___f_5425_; lean_object* v___x_5426_; uint8_t v___x_5427_; lean_object* v___x_5428_; 
lean_inc(v_n_5418_);
lean_inc_ref(v_type_5419_);
v___f_5425_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5425_, 0, v_type_5419_);
lean_closure_set(v___f_5425_, 1, v_n_5418_);
v___x_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5426_, 0, v_n_5418_);
v___x_5427_ = 0;
v___x_5428_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5419_, v___x_5426_, v___f_5425_, v___x_5427_, v___x_5427_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5429_, lean_object* v_type_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Lean_Meta_arrowDomainsN(v_n_5429_, v_type_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5437_, lean_object* v_e_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_){
_start:
{
lean_object* v___x_5444_; 
lean_inc(v_a_5442_);
lean_inc_ref(v_a_5441_);
lean_inc(v_a_5440_);
lean_inc_ref(v_a_5439_);
v___x_5444_ = lean_infer_type(v_e_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5446_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref_known(v___x_5444_, 1);
v___x_5446_ = l_Lean_Meta_arrowDomainsN(v_n_5437_, v_a_5445_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
return v___x_5446_;
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_n_5437_);
v_a_5447_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5444_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5444_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5455_, lean_object* v_e_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Meta_inferArgumentTypesN(v_n_5455_, v_e_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_);
lean_dec(v_a_5460_);
lean_dec_ref(v_a_5459_);
lean_dec(v_a_5458_);
lean_dec_ref(v_a_5457_);
return v_res_5462_;
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
