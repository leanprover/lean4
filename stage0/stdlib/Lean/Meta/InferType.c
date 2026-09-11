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
v___x_985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_env_1031_; uint8_t v___x_1032_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_st_ref_get(v___y_1027_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_env_1031_);
lean_dec(v___x_1030_);
v___x_1032_ = l_Lean_Name_isAnonymous(v_declHint_1026_);
if (v___x_1032_ == 0)
{
uint8_t v_isExporting_1033_; 
v_isExporting_1033_ = lean_ctor_get_uint8(v_env_1031_, sizeof(void*)*8);
if (v_isExporting_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v_env_1031_);
lean_dec(v_declHint_1026_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_msg_1025_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
lean_inc_ref(v_env_1031_);
v___x_1035_ = l_Lean_Environment_setExporting(v_env_1031_, v___x_1032_);
lean_inc(v_declHint_1026_);
lean_inc_ref(v___x_1035_);
v___x_1036_ = l_Lean_Environment_contains(v___x_1035_, v_declHint_1026_, v_isExporting_1033_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v___x_1035_);
lean_dec_ref(v_env_1031_);
lean_dec(v_declHint_1026_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_msg_1025_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_c_1043_; lean_object* v___x_1044_; 
v___x_1038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1040_ = l_Lean_Options_empty;
v___x_1041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1035_);
lean_ctor_set(v___x_1041_, 1, v___x_1038_);
lean_ctor_set(v___x_1041_, 2, v___x_1039_);
lean_ctor_set(v___x_1041_, 3, v___x_1040_);
lean_inc(v_declHint_1026_);
v___x_1042_ = l_Lean_MessageData_ofConstName(v_declHint_1026_, v___x_1032_);
v_c_1043_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1043_, 0, v___x_1041_);
lean_ctor_set(v_c_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1031_, v_declHint_1026_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_env_1031_);
lean_dec(v_declHint_1026_);
v___x_1045_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_c_1043_);
v___x_1047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_MessageData_note(v___x_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_msg_1025_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v_val_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1086_; 
v_val_1052_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1054_ = v___x_1044_;
v_isShared_1055_ = v_isSharedCheck_1086_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_val_1052_);
lean_dec(v___x_1044_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1086_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mod_1058_; uint8_t v___x_1059_; 
v___x_1056_ = l_Lean_Environment_header(v_env_1031_);
lean_dec_ref(v_env_1031_);
v___x_1057_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1056_);
v_mod_1058_ = lean_array_get(v___x_1029_, v___x_1057_, v_val_1052_);
lean_dec(v_val_1052_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_isPrivateName(v_declHint_1026_);
lean_dec(v_declHint_1026_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_c_1043_);
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
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1069_);
v___x_1071_ = v___x_1054_;
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
lean_ctor_set(v___x_1074_, 1, v_c_1043_);
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
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1082_);
v___x_1084_ = v___x_1054_;
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
lean_dec_ref(v_env_1031_);
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
v___x_1747_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1151__boxed_1851_; size_t v_x_1152__boxed_1852_; lean_object* v_res_1853_; 
v_x_1151__boxed_1851_ = lean_unbox_usize(v_x_1847_);
lean_dec(v_x_1847_);
v_x_1152__boxed_1852_ = lean_unbox_usize(v_x_1848_);
lean_dec(v_x_1848_);
v_res_1853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1846_, v_x_1151__boxed_1851_, v_x_1152__boxed_1852_, v_x_1849_, v_x_1850_);
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
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1882_, v_mvarId_1861_, v_val_1862_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 8, v___x_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
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
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_dAssignment_1883_);
lean_ctor_set(v_reuseFailAlloc_1897_, 10, v_instanceTypedMVars_1884_);
v___x_1891_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1891_);
v___x_1893_ = v___x_1872_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_cache_1867_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_zetaDeltaFVarIds_1868_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_postponed_1869_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_diag_1870_);
v___x_1893_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_st_ref_put(v___y_1863_, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1888_);
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
size_t v_x_1500__boxed_2006_; size_t v_x_1501__boxed_2007_; lean_object* v_res_2008_; 
v_x_1500__boxed_2006_ = lean_unbox_usize(v_x_2002_);
lean_dec(v_x_2002_);
v_x_1501__boxed_2007_ = lean_unbox_usize(v_x_2003_);
lean_dec(v_x_2003_);
v_res_2008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2000_, v_x_2001_, v_x_1500__boxed_2006_, v_x_1501__boxed_2007_, v_x_2004_, v_x_2005_);
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
v___x_2433_ = l_instMonadEIO___redArg();
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
v___x_2438_ = l_instMonadExceptOfEIO___redArg();
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
lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___f_2503_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2505_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2455_, v_a_2457_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2603_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2603_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2603_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2550_; lean_object* v_cache_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2598_; 
v___x_2550_ = lean_st_ref_get(v_a_2458_);
v_cache_2551_ = lean_ctor_get(v___x_2550_, 1);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; 
v_unused_2599_ = lean_ctor_get(v___x_2550_, 4);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v___x_2550_, 3);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v___x_2550_, 2);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2602_);
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2598_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_cache_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2598_;
goto v_resetjp_2552_;
}
v___jp_2510_:
{
lean_object* v___x_2511_; 
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
v___x_2511_ = lean_apply_5(v_inferType_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, lean_box(0));
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; uint8_t v___x_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
v___x_2513_ = l_Lean_Expr_hasMVar(v_a_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2548_; 
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v___x_2511_, 0);
lean_dec(v_unused_2549_);
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2548_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2548_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v_cache_2518_; lean_object* v_mctx_2519_; lean_object* v_zetaDeltaFVarIds_2520_; lean_object* v_postponed_2521_; lean_object* v_diag_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2547_; 
v___x_2517_ = lean_st_ref_take(v_a_2458_);
v_cache_2518_ = lean_ctor_get(v___x_2517_, 1);
v_mctx_2519_ = lean_ctor_get(v___x_2517_, 0);
v_zetaDeltaFVarIds_2520_ = lean_ctor_get(v___x_2517_, 2);
v_postponed_2521_ = lean_ctor_get(v___x_2517_, 3);
v_diag_2522_ = lean_ctor_get(v___x_2517_, 4);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2524_ = v___x_2517_;
v_isShared_2525_ = v_isSharedCheck_2547_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_diag_2522_);
lean_inc(v_postponed_2521_);
lean_inc(v_zetaDeltaFVarIds_2520_);
lean_inc(v_cache_2518_);
lean_inc(v_mctx_2519_);
lean_dec(v___x_2517_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2547_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_inferType_2526_; lean_object* v_funInfo_2527_; lean_object* v_synthInstance_2528_; lean_object* v_whnf_2529_; lean_object* v_defEqTrans_2530_; lean_object* v_defEqPerm_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2546_; 
v_inferType_2526_ = lean_ctor_get(v_cache_2518_, 0);
v_funInfo_2527_ = lean_ctor_get(v_cache_2518_, 1);
v_synthInstance_2528_ = lean_ctor_get(v_cache_2518_, 2);
v_whnf_2529_ = lean_ctor_get(v_cache_2518_, 3);
v_defEqTrans_2530_ = lean_ctor_get(v_cache_2518_, 4);
v_defEqPerm_2531_ = lean_ctor_get(v_cache_2518_, 5);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_cache_2518_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2533_ = v_cache_2518_;
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_defEqPerm_2531_);
lean_inc(v_defEqTrans_2530_);
lean_inc(v_whnf_2529_);
lean_inc(v_synthInstance_2528_);
lean_inc(v_funInfo_2527_);
lean_inc(v_inferType_2526_);
lean_dec(v_cache_2518_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2546_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_inc(v_a_2512_);
v___x_2535_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2503_, v___x_2504_, v_inferType_2526_, v_a_2506_, v_a_2512_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_funInfo_2527_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_synthInstance_2528_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_whnf_2529_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_defEqTrans_2530_);
lean_ctor_set(v_reuseFailAlloc_2545_, 5, v_defEqPerm_2531_);
v___x_2537_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2537_);
v___x_2539_ = v___x_2524_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_mctx_2519_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_zetaDeltaFVarIds_2520_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_postponed_2521_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_diag_2522_);
v___x_2539_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_st_ref_put(v_a_2458_, v___x_2539_);
if (v_isShared_2516_ == 0)
{
v___x_2542_ = v___x_2515_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2512_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2512_);
lean_dec(v_a_2506_);
return v___x_2511_;
}
}
else
{
lean_dec(v_a_2506_);
return v___x_2511_;
}
}
v_resetjp_2552_:
{
lean_object* v_inferType_2555_; lean_object* v___x_2556_; 
v_inferType_2555_ = lean_ctor_get(v_cache_2551_, 0);
lean_inc_ref(v_inferType_2555_);
lean_dec_ref(v_cache_2551_);
lean_inc(v_a_2506_);
v___x_2556_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2503_, v___x_2504_, v_inferType_2555_, v_a_2506_);
lean_dec_ref(v_inferType_2555_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; lean_object* v_toApplicative_2558_; lean_object* v_toFunctor_2559_; lean_object* v_toSeq_2560_; lean_object* v_toSeqLeft_2561_; lean_object* v_toSeqRight_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2572_; 
lean_del_object(v___x_2508_);
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
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___f_2568_);
lean_ctor_set(v___x_2553_, 3, v___f_2569_);
lean_ctor_set(v___x_2553_, 2, v___f_2570_);
lean_ctor_set(v___x_2553_, 1, v___f_2563_);
lean_ctor_set(v___x_2553_, 0, v___x_2567_);
v___x_2572_ = v___x_2553_;
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
goto v___jp_2510_;
}
else
{
lean_object* v___x_2060__overap_2583_; lean_object* v___x_2584_; 
v___x_2060__overap_2583_ = l_Lean_throwInterruptException___redArg(v___x_2578_);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
v___x_2584_ = lean_apply_3(v___x_2060__overap_2583_, v_a_2459_, v_a_2460_, lean_box(0));
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
goto v___jp_2510_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2506_);
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
goto v___jp_2510_;
}
}
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; 
lean_del_object(v___x_2553_);
lean_dec(v_a_2506_);
lean_dec_ref(v_inferType_2456_);
v_val_2594_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_val_2594_);
lean_dec_ref_known(v___x_2556_, 1);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v_val_2594_);
v___x_2596_ = v___x_2508_;
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
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v_inferType_2456_);
v_a_2604_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2505_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2505_);
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
lean_object* v___x_2032__overap_2489_; lean_object* v___x_2490_; 
v___x_2032__overap_2489_ = l_Lean_throwInterruptException___redArg(v___x_2483_);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
v___x_2490_ = lean_apply_3(v___x_2032__overap_2489_, v_a_2459_, v_a_2460_, lean_box(0));
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
v___x_2929_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
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
size_t v_x_2794__boxed_2968_; size_t v_x_2795__boxed_2969_; lean_object* v_res_2970_; 
v_x_2794__boxed_2968_ = lean_unbox_usize(v_x_2964_);
lean_dec(v_x_2964_);
v_x_2795__boxed_2969_ = lean_unbox_usize(v_x_2965_);
lean_dec(v_x_2965_);
v_res_2970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2963_, v_x_2794__boxed_2968_, v_x_2795__boxed_2969_, v_x_2966_, v_x_2967_);
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
size_t v_x_2998__boxed_3040_; lean_object* v_res_3041_; 
v_x_2998__boxed_3040_ = lean_unbox_usize(v_x_3038_);
lean_dec(v_x_3038_);
v_res_3041_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3037_, v_x_2998__boxed_3040_, v_x_3039_);
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
size_t v_x_4036__boxed_3593_; size_t v_x_4037__boxed_3594_; lean_object* v_res_3595_; 
v_x_4036__boxed_3593_ = lean_unbox_usize(v_x_3589_);
lean_dec(v_x_3589_);
v_x_4037__boxed_3594_ = lean_unbox_usize(v_x_3590_);
lean_dec(v_x_3590_);
v_res_3595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3587_, v_x_3588_, v_x_4036__boxed_3593_, v_x_4037__boxed_3594_, v_x_3591_, v_x_3592_);
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
size_t v_x_4053__boxed_3605_; lean_object* v_res_3606_; 
v_x_4053__boxed_3605_ = lean_unbox_usize(v_x_3603_);
lean_dec(v_x_3603_);
v_res_3606_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3601_, v_x_3602_, v_x_4053__boxed_3605_, v_x_3604_);
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
lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4934_ = lean_box(0);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v_cache_4923_);
v___x_4936_ = v___x_4932_;
goto v_reusejp_4935_;
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
v___x_4936_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = lean_st_ref_put(v_a_4922_, v___x_4936_);
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4934_);
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
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v_cache_4956_; lean_object* v___x_4957_; 
v___x_4954_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4955_ = lean_st_ref_get(v_a_4949_);
v_cache_4956_ = lean_ctor_get(v___x_4955_, 1);
lean_inc_ref(v_cache_4956_);
lean_dec(v___x_4955_);
v___x_4957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4947_, v___x_4954_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
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
v___x_4964_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4949_, v_cache_4956_, v___x_4963_);
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
v___x_4977_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4949_, v_cache_4956_, v___x_4976_);
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
lean_object* v_v_5293_; lean_object* v___x_5294_; lean_object* v_bs_x27_5295_; lean_object* v___x_5296_; 
v_v_5293_ = lean_array_uget(v_bs_5285_, v_i_5284_);
v___x_5294_ = lean_unsigned_to_nat(0u);
v_bs_x27_5295_ = lean_array_uset(v_bs_5285_, v_i_5284_, v___x_5294_);
lean_inc(v___y_5289_);
lean_inc_ref(v___y_5288_);
lean_inc(v___y_5287_);
lean_inc_ref(v___y_5286_);
v___x_5296_ = lean_infer_type(v_v_5293_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; size_t v___x_5298_; size_t v___x_5299_; lean_object* v___x_5300_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_a_5297_);
lean_dec_ref_known(v___x_5296_, 1);
v___x_5298_ = ((size_t)1ULL);
v___x_5299_ = lean_usize_add(v_i_5284_, v___x_5298_);
v___x_5300_ = lean_array_uset(v_bs_x27_5295_, v_i_5284_, v_a_5297_);
v_i_5284_ = v___x_5299_;
v_bs_5285_ = v___x_5300_;
goto _start;
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec_ref(v_bs_x27_5295_);
v_a_5302_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5296_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5296_);
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
