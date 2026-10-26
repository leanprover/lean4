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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
uint8_t l_Lean_Level_isNeverZero(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Expr.instantiateBetaRevRange"};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__0 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__0_value;
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 42, .m_data = "assertion violation: stop ≤ args.size\n    "};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__1_value;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_applyList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* v_key_81_; lean_object* v_tail_82_; lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; uint8_t v___x_87_; 
v_key_81_ = lean_ctor_get(v_x_79_, 0);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v_fst_83_ = lean_ctor_get(v_key_81_, 0);
v_snd_84_ = lean_ctor_get(v_key_81_, 1);
v_fst_85_ = lean_ctor_get(v_a_78_, 0);
v_snd_86_ = lean_ctor_get(v_a_78_, 1);
v___x_87_ = l_Lean_ExprStructEq_beq(v_fst_83_, v_fst_85_);
if (v___x_87_ == 0)
{
v_x_79_ = v_tail_82_;
goto _start;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_eq(v_snd_84_, v_snd_86_);
if (v___x_89_ == 0)
{
v_x_79_ = v_tail_82_;
goto _start;
}
else
{
return v___x_89_;
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
lean_object* v_key_98_; lean_object* v_value_99_; lean_object* v_tail_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_116_; 
v_key_98_ = lean_ctor_get(v_x_97_, 0);
v_value_99_ = lean_ctor_get(v_x_97_, 1);
v_tail_100_ = lean_ctor_get(v_x_97_, 2);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_116_ == 0)
{
v___x_102_ = v_x_97_;
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_tail_100_);
lean_inc(v_value_99_);
lean_inc(v_key_98_);
lean_dec(v_x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v_fst_111_; lean_object* v_snd_112_; uint8_t v___x_113_; 
v_fst_109_ = lean_ctor_get(v_key_98_, 0);
v_snd_110_ = lean_ctor_get(v_key_98_, 1);
v_fst_111_ = lean_ctor_get(v_a_95_, 0);
v_snd_112_ = lean_ctor_get(v_a_95_, 1);
v___x_113_ = l_Lean_ExprStructEq_beq(v_fst_109_, v_fst_111_);
if (v___x_113_ == 0)
{
goto v___jp_104_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = lean_nat_dec_eq(v_snd_110_, v_snd_112_);
if (v___x_114_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v___x_115_; 
lean_del_object(v___x_102_);
lean_dec(v_value_99_);
lean_dec(v_key_98_);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v_a_95_);
lean_ctor_set(v___x_115_, 1, v_b_96_);
lean_ctor_set(v___x_115_, 2, v_tail_100_);
return v___x_115_;
}
}
v___jp_104_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_95_, v_b_96_, v_tail_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_105_);
v___x_107_ = v___x_102_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_key_98_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_value_99_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object* v_m_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v_size_120_; lean_object* v_buckets_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_168_; 
v_size_120_ = lean_ctor_get(v_m_117_, 0);
v_buckets_121_ = lean_ctor_get(v_m_117_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_m_117_);
if (v_isSharedCheck_168_ == 0)
{
v___x_123_ = v_m_117_;
v_isShared_124_ = v_isSharedCheck_168_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_buckets_121_);
lean_inc(v_size_120_);
lean_dec(v_m_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_168_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v_fold_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v_bkt_142_; uint8_t v___x_143_; 
v_fst_125_ = lean_ctor_get(v_a_118_, 0);
v_snd_126_ = lean_ctor_get(v_a_118_, 1);
v___x_127_ = lean_array_get_size(v_buckets_121_);
v___x_128_ = l_Lean_ExprStructEq_hash(v_fst_125_);
v___x_129_ = lean_uint64_of_nat(v_snd_126_);
v___x_130_ = lean_uint64_mix_hash(v___x_128_, v___x_129_);
v___x_131_ = 32ULL;
v___x_132_ = lean_uint64_shift_right(v___x_130_, v___x_131_);
v_fold_133_ = lean_uint64_xor(v___x_130_, v___x_132_);
v___x_134_ = 16ULL;
v___x_135_ = lean_uint64_shift_right(v_fold_133_, v___x_134_);
v___x_136_ = lean_uint64_xor(v_fold_133_, v___x_135_);
v___x_137_ = lean_uint64_to_usize(v___x_136_);
v___x_138_ = lean_usize_of_nat(v___x_127_);
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_sub(v___x_138_, v___x_139_);
v___x_141_ = lean_usize_land(v___x_137_, v___x_140_);
v_bkt_142_ = lean_array_uget_borrowed(v_buckets_121_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_118_, v_bkt_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v_size_x27_145_; lean_object* v___x_146_; lean_object* v_buckets_x27_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v_size_x27_145_ = lean_nat_add(v_size_120_, v___x_144_);
lean_dec(v_size_120_);
lean_inc(v_bkt_142_);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v_a_118_);
lean_ctor_set(v___x_146_, 1, v_b_119_);
lean_ctor_set(v___x_146_, 2, v_bkt_142_);
v_buckets_x27_147_ = lean_array_uset(v_buckets_121_, v___x_141_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_mul(v_size_x27_145_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(3u);
v___x_151_ = lean_nat_div(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_array_get_size(v_buckets_x27_147_);
v___x_153_ = lean_nat_dec_le(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v_val_154_; lean_object* v___x_156_; 
v_val_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_buckets_x27_147_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_val_154_);
lean_ctor_set(v___x_123_, 0, v_size_x27_145_);
v___x_156_ = v___x_123_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_val_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
else
{
lean_object* v___x_159_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_buckets_x27_147_);
lean_ctor_set(v___x_123_, 0, v_size_x27_145_);
v___x_159_ = v___x_123_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_buckets_x27_147_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v___x_161_; lean_object* v_buckets_x27_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_inc(v_bkt_142_);
v___x_161_ = lean_box(0);
v_buckets_x27_162_ = lean_array_uset(v_buckets_121_, v___x_141_, v___x_161_);
v___x_163_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_118_, v_b_119_, v_bkt_142_);
v___x_164_ = lean_array_uset(v_buckets_x27_162_, v___x_141_, v___x_163_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_164_);
v___x_166_ = v___x_123_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_120_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(lean_object* v_msg_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = l_Lean_instInhabitedExpr;
v___x_171_ = lean_panic_fn_borrowed(v___x_170_, v_msg_169_);
return v___x_171_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1(void){
_start:
{
lean_object* v___x_173_; lean_object* v___f_174_; 
v___x_173_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_174_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_174_, 0, v___x_173_);
return v___f_174_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_4808__overap_205_; lean_object* v___x_206_; 
v___x_186_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_187_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1);
v___f_188_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_188_, 0, v___x_186_);
lean_closure_set(v___f_188_, 1, v___f_187_);
v___x_189_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_190_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_191_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_191_, 0, v___x_189_);
lean_closure_set(v___f_191_, 1, v___f_190_);
v___f_192_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_193_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_194_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___f_195_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7));
v___f_196_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8));
v___f_197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9));
v___f_198_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10));
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___f_192_);
lean_ctor_set(v___x_199_, 1, v___f_193_);
v___x_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___f_194_);
lean_ctor_set(v___x_200_, 2, v___f_195_);
lean_ctor_set(v___x_200_, 3, v___f_196_);
lean_ctor_set(v___x_200_, 4, v___f_197_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___f_198_);
v___x_202_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_188_, v___f_191_, v___x_201_);
v___x_203_ = l_Lean_instInhabitedExpr;
v___x_204_ = l_instInhabitedOfMonad___redArg(v___x_202_, v___x_203_);
v___x_4808__overap_205_ = lean_panic_fn_borrowed(v___x_204_, v_msg_184_);
lean_dec(v___x_204_);
v___x_206_ = lean_apply_1(v___x_4808__overap_205_, v___y_185_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v_key_210_; lean_object* v_value_211_; lean_object* v_tail_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v_fst_215_; lean_object* v_snd_216_; uint8_t v___x_217_; 
v_key_210_ = lean_ctor_get(v_x_208_, 0);
v_value_211_ = lean_ctor_get(v_x_208_, 1);
v_tail_212_ = lean_ctor_get(v_x_208_, 2);
v_fst_213_ = lean_ctor_get(v_key_210_, 0);
v_snd_214_ = lean_ctor_get(v_key_210_, 1);
v_fst_215_ = lean_ctor_get(v_a_207_, 0);
v_snd_216_ = lean_ctor_get(v_a_207_, 1);
v___x_217_ = l_Lean_ExprStructEq_beq(v_fst_213_, v_fst_215_);
if (v___x_217_ == 0)
{
v_x_208_ = v_tail_212_;
goto _start;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = lean_nat_dec_eq(v_snd_214_, v_snd_216_);
if (v___x_219_ == 0)
{
v_x_208_ = v_tail_212_;
goto _start;
}
else
{
lean_object* v___x_221_; 
lean_inc(v_value_211_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_value_211_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec_ref(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_buckets_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_buckets_227_ = lean_ctor_get(v_m_225_, 1);
v_fst_228_ = lean_ctor_get(v_a_226_, 0);
v_snd_229_ = lean_ctor_get(v_a_226_, 1);
v___x_230_ = lean_array_get_size(v_buckets_227_);
v___x_231_ = l_Lean_ExprStructEq_hash(v_fst_228_);
v___x_232_ = lean_uint64_of_nat(v_snd_229_);
v___x_233_ = lean_uint64_mix_hash(v___x_231_, v___x_232_);
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___x_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___x_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_230_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_buckets_227_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_226_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object* v_m_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_247_, v_a_248_);
lean_dec_ref(v_a_248_);
lean_dec_ref(v_m_247_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_254_ = lean_unsigned_to_nat(21u);
v___x_255_ = lean_unsigned_to_nat(96u);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_258_ = l_mkPanicMessageWithDecl(v___x_257_, v___x_256_, v___x_255_, v___x_254_, v___x_253_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_260_ = lean_unsigned_to_nat(21u);
v___x_261_ = lean_unsigned_to_nat(97u);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_264_ = l_mkPanicMessageWithDecl(v___x_263_, v___x_262_, v___x_261_, v___x_260_, v___x_259_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_266_ = lean_unsigned_to_nat(21u);
v___x_267_ = lean_unsigned_to_nat(98u);
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_270_ = l_mkPanicMessageWithDecl(v___x_269_, v___x_268_, v___x_267_, v___x_266_, v___x_265_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_272_ = lean_unsigned_to_nat(21u);
v___x_273_ = lean_unsigned_to_nat(95u);
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_276_ = l_mkPanicMessageWithDecl(v___x_275_, v___x_274_, v___x_273_, v___x_272_, v___x_271_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object* v_start_277_, lean_object* v_stop_278_, lean_object* v_args_279_, lean_object* v_e_280_, lean_object* v_offset_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_Lean_Expr_looseBVarRange(v_e_280_);
v___x_284_ = lean_nat_dec_le(v___x_283_, v_offset_281_);
lean_dec(v___x_283_);
if (v___x_284_ == 0)
{
if (lean_obj_tag(v_e_280_) == 5)
{
lean_object* v_fn_285_; lean_object* v_arg_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_fn_285_ = lean_ctor_get(v_e_280_, 0);
lean_inc_ref(v_fn_285_);
v_arg_286_ = lean_ctor_get(v_e_280_, 1);
lean_inc_ref(v_arg_286_);
lean_inc(v_offset_281_);
lean_inc_ref(v_e_280_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_e_280_);
lean_ctor_set(v___x_287_, 1, v_offset_281_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_282_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_289_; lean_object* v_fst_290_; lean_object* v_snd_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
v___x_289_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_277_, v_stop_278_, v_args_279_, v_e_280_, v_fn_285_, v_arg_286_, v_offset_281_, v_a_282_);
v_fst_290_ = lean_ctor_get(v___x_289_, 0);
v_snd_291_ = lean_ctor_get(v___x_289_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v___x_289_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_snd_291_);
lean_inc(v_fst_290_);
lean_dec(v___x_289_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_inc(v_fst_290_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_291_, v___x_287_, v_fst_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_fst_290_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; 
lean_dec_ref_known(v___x_287_, 2);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_fn_285_);
lean_dec_ref_known(v_e_280_, 2);
lean_dec(v_offset_281_);
v_val_300_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_288_, 1);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_val_300_);
lean_ctor_set(v___x_301_, 1, v_a_282_);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_277_, v_stop_278_, v_args_279_, v_e_280_, v_offset_281_, v_a_282_);
return v___x_302_;
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v_offset_281_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_e_280_);
lean_ctor_set(v___x_303_, 1, v_a_282_);
return v___x_303_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2));
v___x_308_ = lean_unsigned_to_nat(18u);
v___x_309_ = lean_unsigned_to_nat(1870u);
v___x_310_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_312_ = l_mkPanicMessageWithDecl(v___x_311_, v___x_310_, v___x_309_, v___x_308_, v___x_307_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_313_, lean_object* v_stop_314_, lean_object* v_args_315_, lean_object* v_e_316_, lean_object* v_f_317_, lean_object* v_a_318_, lean_object* v_offset_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___x_324_; 
lean_inc(v_offset_319_);
v___x_321_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_313_, v_stop_314_, v_args_315_, v_f_317_, v_offset_319_, v_a_320_);
v_fst_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_snd_323_);
lean_dec_ref(v___x_321_);
v___x_324_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_313_, v_stop_314_, v_args_315_, v_a_318_, v_offset_319_, v_snd_323_);
if (lean_obj_tag(v_e_316_) == 5)
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_349_; 
v_fst_325_ = lean_ctor_get(v___x_324_, 0);
v_snd_326_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_349_ == 0)
{
v___x_328_ = v___x_324_;
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v___x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fn_330_; lean_object* v_arg_331_; size_t v___x_332_; size_t v___x_333_; uint8_t v___x_334_; 
v_fn_330_ = lean_ctor_get(v_e_316_, 0);
v_arg_331_ = lean_ctor_get(v_e_316_, 1);
v___x_332_ = lean_ptr_addr(v_fn_330_);
v___x_333_ = lean_ptr_addr(v_fst_322_);
v___x_334_ = lean_usize_dec_eq(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_dec_ref_known(v_e_316_, 2);
v___x_335_ = l_Lean_Expr_app___override(v_fst_322_, v_fst_325_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_337_ = v___x_328_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_snd_326_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
size_t v___x_339_; size_t v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_ptr_addr(v_arg_331_);
v___x_340_ = lean_ptr_addr(v_fst_325_);
v___x_341_ = lean_usize_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec_ref_known(v_e_316_, 2);
v___x_342_ = l_Lean_Expr_app___override(v_fst_322_, v_fst_325_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_342_);
v___x_344_ = v___x_328_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_326_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec(v_fst_325_);
lean_dec(v_fst_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_e_316_);
v___x_347_ = v___x_328_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_e_316_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_snd_326_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
else
{
lean_object* v_snd_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_fst_322_);
lean_dec_ref(v_e_316_);
v_snd_350_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v___x_324_, 0);
lean_dec(v_unused_360_);
v___x_352_ = v___x_324_;
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_snd_350_);
lean_dec(v___x_324_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_355_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_354_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_355_);
v___x_357_ = v___x_352_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_snd_350_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
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
lean_object* v_binderName_413_; lean_object* v_binderType_414_; lean_object* v_body_415_; uint8_t v_binderInfo_416_; lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; size_t v___x_425_; size_t v___x_426_; uint8_t v___x_427_; 
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
v___x_425_ = lean_ptr_addr(v_binderType_414_);
v___x_426_ = lean_ptr_addr(v_fst_418_);
v___x_427_ = lean_usize_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_inc(v_binderName_413_);
lean_dec_ref_known(v_e_370_, 3);
v___x_428_ = l_Lean_Expr_lam___override(v_binderName_413_, v_fst_418_, v_fst_423_, v_binderInfo_416_);
v_fst_377_ = v___x_428_;
v_snd_378_ = v_snd_424_;
goto v___jp_376_;
}
else
{
size_t v___x_429_; size_t v___x_430_; uint8_t v___x_431_; 
v___x_429_ = lean_ptr_addr(v_body_415_);
v___x_430_ = lean_ptr_addr(v_fst_423_);
v___x_431_ = lean_usize_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v_binderName_413_);
lean_dec_ref_known(v_e_370_, 3);
v___x_432_ = l_Lean_Expr_lam___override(v_binderName_413_, v_fst_418_, v_fst_423_, v_binderInfo_416_);
v_fst_377_ = v___x_432_;
v_snd_378_ = v_snd_424_;
goto v___jp_376_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_416_, v_binderInfo_416_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_inc(v_binderName_413_);
lean_dec_ref_known(v_e_370_, 3);
v___x_434_ = l_Lean_Expr_lam___override(v_binderName_413_, v_fst_418_, v_fst_423_, v_binderInfo_416_);
v_fst_377_ = v___x_434_;
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
lean_object* v_binderName_435_; lean_object* v_binderType_436_; lean_object* v_body_437_; uint8_t v_binderInfo_438_; lean_object* v___x_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_fst_445_; lean_object* v_snd_446_; size_t v___x_447_; size_t v___x_448_; uint8_t v___x_449_; 
v_binderName_435_ = lean_ctor_get(v_e_370_, 0);
v_binderType_436_ = lean_ctor_get(v_e_370_, 1);
v_body_437_ = lean_ctor_get(v_e_370_, 2);
v_binderInfo_438_ = lean_ctor_get_uint8(v_e_370_, sizeof(void*)*3 + 8);
lean_inc(v_offset_371_);
lean_inc_ref(v_binderType_436_);
v___x_439_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_binderType_436_, v_offset_371_, v_a_372_);
v_fst_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_snd_441_);
lean_dec_ref(v___x_439_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_offset_371_, v___x_442_);
lean_dec(v_offset_371_);
lean_inc_ref(v_body_437_);
v___x_444_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_body_437_, v___x_443_, v_snd_441_);
v_fst_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v___x_444_, 1);
lean_inc(v_snd_446_);
lean_dec_ref(v___x_444_);
v___x_447_ = lean_ptr_addr(v_binderType_436_);
v___x_448_ = lean_ptr_addr(v_fst_440_);
v___x_449_ = lean_usize_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v_e_370_, 3);
v___x_450_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_fst_440_, v_fst_445_, v_binderInfo_438_);
v_fst_377_ = v___x_450_;
v_snd_378_ = v_snd_446_;
goto v___jp_376_;
}
else
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_ptr_addr(v_body_437_);
v___x_452_ = lean_ptr_addr(v_fst_445_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v_e_370_, 3);
v___x_454_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_fst_440_, v_fst_445_, v_binderInfo_438_);
v_fst_377_ = v___x_454_;
v_snd_378_ = v_snd_446_;
goto v___jp_376_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_438_, v_binderInfo_438_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v_e_370_, 3);
v___x_456_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_fst_440_, v_fst_445_, v_binderInfo_438_);
v_fst_377_ = v___x_456_;
v_snd_378_ = v_snd_446_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_445_);
lean_dec(v_fst_440_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_446_;
goto v___jp_376_;
}
}
}
}
case 8:
{
lean_object* v_declName_457_; lean_object* v_type_458_; lean_object* v_value_459_; lean_object* v_body_460_; uint8_t v_nondep_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; size_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v_declName_457_ = lean_ctor_get(v_e_370_, 0);
v_type_458_ = lean_ctor_get(v_e_370_, 1);
v_value_459_ = lean_ctor_get(v_e_370_, 2);
v_body_460_ = lean_ctor_get(v_e_370_, 3);
v_nondep_461_ = lean_ctor_get_uint8(v_e_370_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_371_, 2);
lean_inc_ref(v_type_458_);
v___x_462_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_type_458_, v_offset_371_, v_a_372_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_fst_463_);
v_snd_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_snd_464_);
lean_dec_ref(v___x_462_);
lean_inc_ref(v_value_459_);
v___x_465_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_value_459_, v_offset_371_, v_snd_464_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___x_465_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_offset_371_, v___x_468_);
lean_dec(v_offset_371_);
lean_inc_ref(v_body_460_);
v___x_470_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_body_460_, v___x_469_, v_snd_467_);
v_fst_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v___x_470_, 1);
lean_inc(v_snd_472_);
lean_dec_ref(v___x_470_);
v___x_473_ = lean_ptr_addr(v_type_458_);
v___x_474_ = lean_ptr_addr(v_fst_463_);
v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_inc(v_declName_457_);
lean_dec_ref_known(v_e_370_, 4);
v___x_476_ = l_Lean_Expr_letE___override(v_declName_457_, v_fst_463_, v_fst_466_, v_fst_471_, v_nondep_461_);
v_fst_377_ = v___x_476_;
v_snd_378_ = v_snd_472_;
goto v___jp_376_;
}
else
{
size_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_ptr_addr(v_value_459_);
v___x_478_ = lean_ptr_addr(v_fst_466_);
v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_inc(v_declName_457_);
lean_dec_ref_known(v_e_370_, 4);
v___x_480_ = l_Lean_Expr_letE___override(v_declName_457_, v_fst_463_, v_fst_466_, v_fst_471_, v_nondep_461_);
v_fst_377_ = v___x_480_;
v_snd_378_ = v_snd_472_;
goto v___jp_376_;
}
else
{
size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_ptr_addr(v_body_460_);
v___x_482_ = lean_ptr_addr(v_fst_471_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_inc(v_declName_457_);
lean_dec_ref_known(v_e_370_, 4);
v___x_484_ = l_Lean_Expr_letE___override(v_declName_457_, v_fst_463_, v_fst_466_, v_fst_471_, v_nondep_461_);
v_fst_377_ = v___x_484_;
v_snd_378_ = v_snd_472_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_471_);
lean_dec(v_fst_466_);
lean_dec(v_fst_463_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_472_;
goto v___jp_376_;
}
}
}
}
case 9:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref_known(v_e_370_, 1);
lean_dec(v_offset_371_);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_486_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_485_, v_a_372_);
v___y_382_ = v___x_486_;
goto v___jp_381_;
}
case 10:
{
lean_object* v_data_487_; lean_object* v_expr_488_; lean_object* v___x_489_; lean_object* v_fst_490_; lean_object* v_snd_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_data_487_ = lean_ctor_get(v_e_370_, 0);
v_expr_488_ = lean_ctor_get(v_e_370_, 1);
lean_inc_ref(v_expr_488_);
v___x_489_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_expr_488_, v_offset_371_, v_a_372_);
v_fst_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_fst_490_);
v_snd_491_ = lean_ctor_get(v___x_489_, 1);
lean_inc(v_snd_491_);
lean_dec_ref(v___x_489_);
v___x_492_ = lean_ptr_addr(v_expr_488_);
v___x_493_ = lean_ptr_addr(v_fst_490_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_inc(v_data_487_);
lean_dec_ref_known(v_e_370_, 2);
v___x_495_ = l_Lean_Expr_mdata___override(v_data_487_, v_fst_490_);
v_fst_377_ = v___x_495_;
v_snd_378_ = v_snd_491_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_490_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_491_;
goto v___jp_376_;
}
}
default: 
{
lean_object* v_typeName_496_; lean_object* v_idx_497_; lean_object* v_struct_498_; lean_object* v___x_499_; lean_object* v_fst_500_; lean_object* v_snd_501_; size_t v___x_502_; size_t v___x_503_; uint8_t v___x_504_; 
v_typeName_496_ = lean_ctor_get(v_e_370_, 0);
v_idx_497_ = lean_ctor_get(v_e_370_, 1);
v_struct_498_ = lean_ctor_get(v_e_370_, 2);
lean_inc_ref(v_struct_498_);
v___x_499_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_367_, v_stop_368_, v_args_369_, v_struct_498_, v_offset_371_, v_a_372_);
v_fst_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_fst_500_);
v_snd_501_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_snd_501_);
lean_dec_ref(v___x_499_);
v___x_502_ = lean_ptr_addr(v_struct_498_);
v___x_503_ = lean_ptr_addr(v_fst_500_);
v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_inc(v_idx_497_);
lean_inc(v_typeName_496_);
lean_dec_ref_known(v_e_370_, 3);
v___x_505_ = l_Lean_Expr_proj___override(v_typeName_496_, v_idx_497_, v_fst_500_);
v_fst_377_ = v___x_505_;
v_snd_378_ = v_snd_501_;
goto v___jp_376_;
}
else
{
lean_dec(v_fst_500_);
v_fst_377_ = v_e_370_;
v_snd_378_ = v_snd_501_;
goto v___jp_376_;
}
}
}
}
else
{
lean_object* v_val_506_; lean_object* v___x_507_; 
lean_dec_ref_known(v___x_375_, 2);
lean_dec(v_offset_371_);
lean_dec_ref(v_e_370_);
v_val_506_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v___x_385_, 1);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_val_506_);
lean_ctor_set(v___x_507_, 1, v_a_372_);
return v___x_507_;
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
lean_object* v___x_508_; 
lean_dec(v_offset_371_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_e_370_);
lean_ctor_set(v___x_508_, 1, v_a_372_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_509_, lean_object* v_stop_510_, lean_object* v_args_511_, lean_object* v_offset_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_bs_515_, lean_object* v___y_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_offset_512_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_bs_515_);
lean_ctor_set(v___x_518_, 1, v___y_516_);
return v___x_518_;
}
else
{
lean_object* v_v_519_; lean_object* v___x_520_; lean_object* v_fst_521_; lean_object* v_snd_522_; lean_object* v___x_523_; lean_object* v_bs_x27_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_v_519_ = lean_array_uget_borrowed(v_bs_515_, v_i_514_);
lean_inc(v_offset_512_);
lean_inc(v_v_519_);
v___x_520_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_509_, v_stop_510_, v_args_511_, v_v_519_, v_offset_512_, v___y_516_);
v_fst_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_fst_521_);
v_snd_522_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_snd_522_);
lean_dec_ref(v___x_520_);
v___x_523_ = lean_unsigned_to_nat(0u);
v_bs_x27_524_ = lean_array_uset(v_bs_515_, v_i_514_, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_514_, v___x_525_);
v___x_527_ = lean_array_uset(v_bs_x27_524_, v_i_514_, v_fst_521_);
v_i_514_ = v___x_526_;
v_bs_515_ = v___x_527_;
v___y_516_ = v_snd_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_529_, lean_object* v_stop_530_, lean_object* v_args_531_, lean_object* v_offset_532_, lean_object* v_sz_533_, lean_object* v_i_534_, lean_object* v_bs_535_, lean_object* v___y_536_){
_start:
{
size_t v_sz_boxed_537_; size_t v_i_boxed_538_; lean_object* v_res_539_; 
v_sz_boxed_537_ = lean_unbox_usize(v_sz_533_);
lean_dec(v_sz_533_);
v_i_boxed_538_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_529_, v_stop_530_, v_args_531_, v_offset_532_, v_sz_boxed_537_, v_i_boxed_538_, v_bs_535_, v___y_536_);
lean_dec_ref(v_args_531_);
lean_dec(v_stop_530_);
lean_dec(v_start_529_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_540_, lean_object* v_stop_541_, lean_object* v_args_542_, lean_object* v_e_543_, lean_object* v_offset_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_540_, v_stop_541_, v_args_542_, v_e_543_, v_offset_544_, v_a_545_);
lean_dec_ref(v_args_542_);
lean_dec(v_stop_541_);
lean_dec(v_start_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_547_, lean_object* v_stop_548_, lean_object* v_args_549_, lean_object* v_e_550_, lean_object* v_f_551_, lean_object* v_a_552_, lean_object* v_offset_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_547_, v_stop_548_, v_args_549_, v_e_550_, v_f_551_, v_a_552_, v_offset_553_, v_a_554_);
lean_dec_ref(v_args_549_);
lean_dec(v_stop_548_);
lean_dec(v_start_547_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_556_, lean_object* v_stop_557_, lean_object* v_args_558_, lean_object* v_e_559_, lean_object* v_offset_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_556_, v_stop_557_, v_args_558_, v_e_559_, v_offset_560_, v_a_561_);
lean_dec_ref(v_args_558_);
lean_dec(v_stop_557_);
lean_dec(v_start_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_563_, lean_object* v_m_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_564_, v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_567_, v_m_568_, v_a_569_);
lean_dec_ref(v_a_569_);
lean_dec_ref(v_m_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_571_, lean_object* v_m_572_, lean_object* v_a_573_, lean_object* v_b_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_572_, v_a_573_, v_b_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_576_, lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_580_, v_a_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec_ref(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_585_, v_x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_588_, lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_588_, v_a_589_, v_x_590_);
lean_dec(v_x_590_);
lean_dec_ref(v_a_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object* v_00_u03b2_593_, lean_object* v_data_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_data_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object* v_00_u03b2_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_597_, v_b_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_601_, lean_object* v_i_602_, lean_object* v_source_603_, lean_object* v_target_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v_i_602_, v_source_603_, v_target_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b2_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_x_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_610_, size_t v_i_611_, size_t v_stop_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_eq(v_i_611_, v_stop_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_array_uget_borrowed(v_as_610_, v_i_611_);
v___x_615_ = l_Lean_Expr_consumeMData(v___x_614_);
v___x_616_ = l_Lean_Expr_isLambda(v___x_615_);
lean_dec_ref(v___x_615_);
if (v___x_616_ == 0)
{
size_t v___x_617_; size_t v___x_618_; 
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_611_, v___x_617_);
v_i_611_ = v___x_618_;
goto _start;
}
else
{
return v___x_616_;
}
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_621_, lean_object* v_i_622_, lean_object* v_stop_623_){
_start:
{
size_t v_i_boxed_624_; size_t v_stop_boxed_625_; uint8_t v_res_626_; lean_object* v_r_627_; 
v_i_boxed_624_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_stop_boxed_625_ = lean_unbox_usize(v_stop_623_);
lean_dec(v_stop_623_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_621_, v_i_boxed_624_, v_stop_boxed_625_);
lean_dec_ref(v_as_621_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__1));
v___x_631_ = lean_unsigned_to_nat(4u);
v___x_632_ = lean_unsigned_to_nat(39u);
v___x_633_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__0));
v___x_634_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_635_ = l_mkPanicMessageWithDecl(v___x_634_, v___x_633_, v___x_632_, v___x_631_, v___x_630_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__3(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_unsigned_to_nat(16u);
v___x_638_ = lean_mk_array(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__3, &l_Lean_Expr_instantiateBetaRevRange___closed__3_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__3);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_642_, lean_object* v_start_643_, lean_object* v_stop_644_, lean_object* v_args_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_Expr_hasLooseBVars(v_e_642_);
if (v___x_646_ == 0)
{
return v_e_642_;
}
else
{
uint8_t v___x_647_; 
v___x_647_ = lean_nat_dec_lt(v_start_643_, v_stop_644_);
if (v___x_647_ == 0)
{
return v_e_642_;
}
else
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_array_get_size(v_args_645_);
v___x_649_ = lean_nat_dec_le(v_stop_644_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref(v_e_642_);
v___x_650_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__2, &l_Lean_Expr_instantiateBetaRevRange___closed__2_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__2);
v___x_651_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_650_);
return v___x_651_;
}
else
{
if (v___x_647_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_expr_instantiate_rev_range(v_e_642_, v_start_643_, v_stop_644_, v_args_645_);
lean_dec_ref(v_e_642_);
return v___x_652_;
}
else
{
size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_usize_of_nat(v_start_643_);
v___x_654_ = lean_usize_of_nat(v_stop_644_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_645_, v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_expr_instantiate_rev_range(v_e_642_, v_start_643_, v_stop_644_, v_args_645_);
lean_dec_ref(v_e_642_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_fst_660_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_659_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_643_, v_stop_644_, v_args_645_, v_e_642_, v___x_657_, v___x_658_);
v_fst_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_fst_660_);
lean_dec_ref(v___x_659_);
return v_fst_660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_661_, lean_object* v_start_662_, lean_object* v_stop_663_, lean_object* v_args_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Expr_instantiateBetaRevRange(v_e_661_, v_start_662_, v_stop_663_, v_args_664_);
lean_dec_ref(v_args_664_);
lean_dec(v_stop_663_);
lean_dec(v_start_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_env_673_; uint8_t v___x_674_; lean_object* v_env_675_; lean_object* v___x_676_; lean_object* v_toCold_677_; lean_object* v_mctx_678_; lean_object* v_lctx_679_; lean_object* v_options_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_672_ = lean_st_ref_get(v___y_670_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_env_673_);
lean_dec(v___x_672_);
v___x_674_ = 0;
v_env_675_ = l_Lean_Environment_setRecordingDeps(v_env_673_, v___x_674_);
v___x_676_ = lean_st_ref_get(v___y_668_);
v_toCold_677_ = lean_ctor_get(v___y_669_, 0);
v_mctx_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_mctx_678_);
lean_dec(v___x_676_);
v_lctx_679_ = lean_ctor_get(v___y_667_, 2);
v_options_680_ = lean_ctor_get(v_toCold_677_, 2);
lean_inc_ref(v_options_680_);
lean_inc_ref(v_lctx_679_);
v___x_681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_681_, 0, v_env_675_);
lean_ctor_set(v___x_681_, 1, v_mctx_678_);
lean_ctor_set(v___x_681_, 2, v_lctx_679_);
lean_ctor_set(v___x_681_, 3, v_options_680_);
v___x_682_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_msgData_666_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_ref_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_ref_697_ = lean_ctor_get(v___y_694_, 2);
v___x_698_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
lean_inc(v_ref_697_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_ref_697_);
lean_ctor_set(v___x_703_, 1, v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 1);
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_725_ = l_Lean_indentExpr(v_f_718_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_726_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_735_, lean_object* v_f_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_743_, lean_object* v_f_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_743_, v_f_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_759_, v_msg_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_767_, lean_object* v_args_768_, lean_object* v_f_769_, lean_object* v_a_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_a_778_; uint8_t v___x_782_; 
v___x_782_ = lean_nat_dec_lt(v_a_770_, v_upperBound_767_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec(v_a_770_);
lean_dec_ref(v_f_769_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_b_771_);
return v___x_783_;
}
else
{
lean_object* v_fst_784_; 
v_fst_784_ = lean_ctor_get(v_b_771_, 0);
lean_inc(v_fst_784_);
if (lean_obj_tag(v_fst_784_) == 7)
{
lean_object* v_snd_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_snd_785_ = lean_ctor_get(v_b_771_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_b_771_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_b_771_, 0);
lean_dec(v_unused_794_);
v___x_787_ = v_b_771_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snd_785_);
lean_dec(v_b_771_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_body_789_; lean_object* v___x_791_; 
v_body_789_ = lean_ctor_get(v_fst_784_, 2);
lean_inc_ref(v_body_789_);
lean_dec_ref_known(v_fst_784_, 3);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_body_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_body_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_785_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_a_778_ = v___x_791_;
goto v___jp_777_;
}
}
}
else
{
lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_830_; 
v_snd_795_ = lean_ctor_get(v_b_771_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_b_771_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v_b_771_, 0);
lean_dec(v_unused_831_);
v___x_797_ = v_b_771_;
v_isShared_798_ = v_isSharedCheck_830_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_dec(v_b_771_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_830_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_784_);
v___x_800_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_784_, v_snd_795_, v_a_770_, v_args_768_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_801_ = lean_whnf(v___x_800_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
if (lean_obj_tag(v_a_802_) == 7)
{
lean_object* v_body_803_; lean_object* v___x_805_; 
lean_dec(v_snd_795_);
lean_dec(v_fst_784_);
v_body_803_ = lean_ctor_get(v_a_802_, 2);
lean_inc_ref(v_body_803_);
lean_dec_ref_known(v_a_802_, 3);
lean_inc(v_a_770_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_a_770_);
lean_ctor_set(v___x_797_, 0, v_body_803_);
v___x_805_ = v___x_797_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_body_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_a_770_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v_a_778_ = v___x_805_;
goto v___jp_777_;
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v_a_802_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_a_770_, v___x_807_);
lean_inc_ref(v_f_769_);
v___x_809_ = l_Lean_mkAppRange(v_f_769_, v___x_799_, v___x_808_, v_args_768_);
lean_dec(v___x_808_);
v___x_810_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_809_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_812_; 
lean_dec_ref_known(v___x_810_, 1);
if (v_isShared_798_ == 0)
{
v___x_812_ = v___x_797_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_784_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_795_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_778_ = v___x_812_;
goto v___jp_777_;
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_784_);
lean_dec(v_a_770_);
lean_dec_ref(v_f_769_);
v_a_814_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_810_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_784_);
lean_dec(v_a_770_);
lean_dec_ref(v_f_769_);
v_a_822_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_801_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_801_);
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
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_a_770_, v___x_779_);
lean_dec(v_a_770_);
v_a_770_ = v___x_780_;
v_b_771_ = v_a_778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_832_, lean_object* v_args_833_, lean_object* v_f_834_, lean_object* v_a_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_832_, v_args_833_, v_f_834_, v_a_835_, v_b_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec_ref(v_args_833_);
lean_dec(v_upperBound_832_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_843_, lean_object* v_args_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
lean_inc(v_a_848_);
lean_inc_ref(v_a_847_);
lean_inc(v_a_846_);
lean_inc_ref(v_a_845_);
lean_inc_ref(v_f_843_);
v___x_850_ = lean_infer_type(v_f_843_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_array_get_size(v_args_844_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v_a_851_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_852_, v_args_844_, v_f_843_, v___x_853_, v___x_854_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v_fst_860_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_fst_860_);
v_snd_861_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_856_);
v___x_862_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_860_, v_snd_861_, v___x_852_, v_args_844_);
lean_dec(v_snd_861_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_862_);
v___x_864_ = v___x_858_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_855_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_855_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_dec_ref(v_f_843_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_875_, lean_object* v_args_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_875_, v_args_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec_ref(v_args_876_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_883_, lean_object* v_args_884_, lean_object* v_f_885_, lean_object* v_inst_886_, lean_object* v_R_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v_c_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_883_, v_args_884_, v_f_885_, v_a_888_, v_b_889_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_897_, lean_object* v_args_898_, lean_object* v_f_899_, lean_object* v_inst_900_, lean_object* v_R_901_, lean_object* v_a_902_, lean_object* v_b_903_, lean_object* v_c_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_897_, v_args_898_, v_f_899_, v_inst_900_, v_R_901_, v_a_902_, v_b_903_, v_c_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec_ref(v_args_898_);
lean_dec(v_upperBound_897_);
return v_res_910_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_914_, lean_object* v_us_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_921_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_922_ = l_Lean_mkConst(v_constName_914_, v_us_915_);
v___x_923_ = l_Lean_MessageData_ofExpr(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_924_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_926_, lean_object* v_us_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_926_, v_us_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_934_, lean_object* v_constName_935_, lean_object* v_us_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_935_, v_us_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_943_, lean_object* v_constName_944_, lean_object* v_us_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_943_, v_constName_944_, v_us_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_952_, lean_object* v_msg_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_toCold_959_; lean_object* v_currRecDepth_960_; lean_object* v_ref_961_; uint16_t v_optionFlags_962_; uint8_t v_suppressElabErrors_963_; uint8_t v_checkDeprecated_964_; uint8_t v_isRecordingDeps_965_; lean_object* v_ref_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_toCold_959_ = lean_ctor_get(v___y_956_, 0);
v_currRecDepth_960_ = lean_ctor_get(v___y_956_, 1);
v_ref_961_ = lean_ctor_get(v___y_956_, 2);
v_optionFlags_962_ = lean_ctor_get_uint16(v___y_956_, sizeof(void*)*3);
v_suppressElabErrors_963_ = lean_ctor_get_uint8(v___y_956_, sizeof(void*)*3 + 2);
v_checkDeprecated_964_ = lean_ctor_get_uint8(v___y_956_, sizeof(void*)*3 + 3);
v_isRecordingDeps_965_ = lean_ctor_get_uint8(v___y_956_, sizeof(void*)*3 + 4);
v_ref_966_ = l_Lean_replaceRef(v_ref_952_, v_ref_961_);
lean_inc(v_currRecDepth_960_);
lean_inc_ref(v_toCold_959_);
v___x_967_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_967_, 0, v_toCold_959_);
lean_ctor_set(v___x_967_, 1, v_currRecDepth_960_);
lean_ctor_set(v___x_967_, 2, v_ref_966_);
lean_ctor_set_uint16(v___x_967_, sizeof(void*)*3, v_optionFlags_962_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 2, v_suppressElabErrors_963_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 3, v_checkDeprecated_964_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 4, v_isRecordingDeps_965_);
v___x_968_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_953_, v___y_954_, v___y_955_, v___x_967_, v___y_957_);
lean_dec_ref_known(v___x_967_, 3);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_969_, v_msg_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v_ref_969_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_980_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
lean_ctor_set(v___x_983_, 4, v___x_981_);
lean_ctor_set(v___x_983_, 5, v___x_981_);
lean_ctor_set(v___x_983_, 6, v___x_981_);
lean_ctor_set(v___x_983_, 7, v___x_981_);
lean_ctor_set(v___x_983_, 8, v___x_981_);
lean_ctor_set(v___x_983_, 9, v___x_981_);
lean_ctor_set(v___x_983_, 10, v___x_981_);
lean_ctor_set(v___x_983_, 11, v___x_980_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_unsigned_to_nat(32u);
v___x_985_ = lean_mk_empty_array_with_capacity(v___x_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = ((size_t)5ULL);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_unsigned_to_nat(32u);
v___x_990_ = lean_mk_empty_array_with_capacity(v___x_989_);
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_992_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
lean_ctor_set(v___x_992_, 2, v___x_988_);
lean_ctor_set(v___x_992_, 3, v___x_988_);
lean_ctor_set_usize(v___x_992_, 4, v___x_987_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = lean_box(1);
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
lean_ctor_set(v___x_996_, 2, v___x_993_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1018_, lean_object* v_declHint_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_env_1024_; uint8_t v___x_1025_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_st_ref_get(v___y_1020_);
v_env_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_env_1024_);
lean_dec(v___x_1023_);
v___x_1025_ = l_Lean_Name_isAnonymous(v_declHint_1019_);
if (v___x_1025_ == 0)
{
uint8_t v_isExporting_1026_; 
v_isExporting_1026_ = lean_ctor_get_uint8(v_env_1024_, sizeof(void*)*13);
if (v_isExporting_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v_env_1024_);
lean_dec(v_declHint_1019_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_msg_1018_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
lean_inc_ref(v_env_1024_);
v___x_1028_ = l_Lean_Environment_setExporting(v_env_1024_, v___x_1025_);
lean_inc(v_declHint_1019_);
lean_inc_ref(v___x_1028_);
v___x_1029_ = l_Lean_Environment_contains(v___x_1028_, v_declHint_1019_, v_isExporting_1026_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
lean_dec_ref(v___x_1028_);
lean_dec_ref(v_env_1024_);
lean_dec(v_declHint_1019_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_msg_1018_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_c_1036_; lean_object* v___x_1037_; 
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1032_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1033_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1028_);
v___x_1034_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
lean_ctor_set(v___x_1034_, 1, v___x_1031_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v___x_1033_);
lean_inc(v_declHint_1019_);
v___x_1035_ = l_Lean_MessageData_ofConstName(v_declHint_1019_, v___x_1025_);
v_c_1036_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1036_, 0, v___x_1034_);
lean_ctor_set(v_c_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1028_, v_declHint_1019_);
lean_dec_ref(v___x_1028_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v_env_1024_);
lean_dec(v_declHint_1019_);
v___x_1038_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_c_1036_);
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_MessageData_note(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_msg_1018_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1079_; 
v_val_1045_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1047_ = v___x_1037_;
v_isShared_1048_ = v_isSharedCheck_1079_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_dec(v___x_1037_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1079_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_moduleNames_1050_; lean_object* v_mod_1051_; uint8_t v___x_1052_; 
v___x_1049_ = l_Lean_Environment_header(v_env_1024_);
lean_dec_ref(v_env_1024_);
v_moduleNames_1050_ = lean_ctor_get(v___x_1049_, 4);
lean_inc_ref(v_moduleNames_1050_);
lean_dec_ref(v___x_1049_);
v_mod_1051_ = lean_array_get(v___x_1022_, v_moduleNames_1050_, v_val_1045_);
lean_dec(v_val_1045_);
lean_dec_ref(v_moduleNames_1050_);
v___x_1052_ = l_Lean_isPrivateName(v_declHint_1019_);
lean_dec(v_declHint_1019_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_c_1036_);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_ofName(v_mod_1051_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_note(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_msg_1018_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1062_);
v___x_1064_ = v___x_1047_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_c_1036_);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_ofName(v_mod_1051_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_MessageData_note(v___x_1073_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_msg_1018_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1075_);
v___x_1077_ = v___x_1047_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1080_; 
lean_dec_ref(v_env_1024_);
lean_dec(v_declHint_1019_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_msg_1018_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1081_, lean_object* v_declHint_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1081_, v_declHint_1082_, v___y_1083_);
lean_dec(v___y_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1086_, lean_object* v_declHint_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1103_; 
v___x_1093_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1086_, v_declHint_1087_, v___y_1091_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1098_ = l_Lean_unknownIdentifierMessageTag;
v___x_1099_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1104_, lean_object* v_declHint_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1104_, v_declHint_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1112_, lean_object* v_msg_1113_, lean_object* v_declHint_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v_a_1121_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1113_, v_declHint_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1112_, v_a_1121_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1123_, lean_object* v_msg_1124_, lean_object* v_declHint_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1123_, v_msg_1124_, v_declHint_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_ref_1123_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1138_, lean_object* v_constName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1145_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1146_ = 0;
lean_inc(v_constName_1139_);
v___x_1147_ = l_Lean_MessageData_ofConstName(v_constName_1139_, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1145_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1138_, v___x_1150_, v_constName_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1152_, lean_object* v_constName_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1152_, v_constName_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_ref_1152_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_ref_1166_; lean_object* v___x_1167_; 
v_ref_1166_ = lean_ctor_get(v___y_1163_, 2);
v___x_1167_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1166_, v_constName_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_env_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = lean_st_ref_get(v___y_1179_);
v_env_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_ref(v_env_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = 0;
lean_inc(v_constName_1175_);
v___x_1184_ = l_Lean_Environment_findConstVal_x3f(v_env_1182_, v_constName_1175_, v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1185_;
}
else
{
lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_constName_1175_);
v_val_1186_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1184_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v___x_1184_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 0);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_val_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1201_, lean_object* v_us_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; 
lean_inc(v_c_1201_);
v___x_1208_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1201_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_levelParams_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v_levelParams_1210_ = lean_ctor_get(v_a_1209_, 1);
v___x_1211_ = l_List_lengthTR___redArg(v_levelParams_1210_);
v___x_1212_ = l_List_lengthTR___redArg(v_us_1202_);
v___x_1213_ = lean_nat_dec_eq(v___x_1211_, v___x_1212_);
lean_dec(v___x_1212_);
lean_dec(v___x_1211_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v_a_1209_);
v___x_1214_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1201_, v_us_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v_c_1201_);
v___x_1215_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1209_, v_us_1202_, v_a_1206_);
return v___x_1215_;
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_us_1202_);
lean_dec(v_c_1201_);
v_a_1216_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1208_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1208_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1224_, lean_object* v_us_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1224_, v_us_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1232_, lean_object* v_constName_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_constName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1240_, v_constName_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1248_, lean_object* v_ref_1249_, lean_object* v_constName_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1249_, v_constName_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_ref_1258_, lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1257_, v_ref_1258_, v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v_ref_1258_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1266_, lean_object* v_ref_1267_, lean_object* v_msg_1268_, lean_object* v_declHint_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1267_, v_msg_1268_, v_declHint_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_ref_1277_, lean_object* v_msg_1278_, lean_object* v_declHint_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1276_, v_ref_1277_, v_msg_1278_, v_declHint_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v_ref_1277_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1286_, lean_object* v_declHint_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1286_, v_declHint_1287_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1303_, v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_ref_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1311_, v_ref_1312_, v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v_ref_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply(lean_object* v_00_u03c3_1320_, lean_object* v_u_1321_){
_start:
{
lean_object* v_paramNames_1322_; lean_object* v_lvls_1323_; uint8_t v___x_1324_; 
v_paramNames_1322_ = lean_ctor_get(v_00_u03c3_1320_, 0);
lean_inc(v_paramNames_1322_);
v_lvls_1323_ = lean_ctor_get(v_00_u03c3_1320_, 1);
lean_inc(v_lvls_1323_);
lean_dec_ref(v_00_u03c3_1320_);
v___x_1324_ = l_List_isEmpty___redArg(v_paramNames_1322_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_Level_instantiateParams(v_u_1321_, v_paramNames_1322_, v_lvls_1323_);
return v___x_1325_;
}
else
{
lean_dec(v_lvls_1323_);
lean_dec(v_paramNames_1322_);
return v_u_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_applyList(lean_object* v_00_u03c3_1326_, lean_object* v_us_1327_){
_start:
{
lean_object* v_paramNames_1328_; uint8_t v___x_1329_; 
v_paramNames_1328_ = lean_ctor_get(v_00_u03c3_1326_, 0);
v___x_1329_ = l_List_isEmpty___redArg(v_paramNames_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply), 2, 1);
lean_closure_set(v___x_1330_, 0, v_00_u03c3_1326_);
v___x_1331_ = lean_box(0);
v___x_1332_ = l_List_mapTR_loop___redArg(v___x_1330_, v_us_1327_, v___x_1331_);
return v___x_1332_;
}
else
{
lean_dec_ref(v_00_u03c3_1326_);
return v_us_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(lean_object* v_c_1333_, lean_object* v_us_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; 
lean_inc(v_c_1333_);
v___x_1340_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_levelParams_1345_; lean_object* v_type_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_levelParams_1345_ = lean_ctor_get(v_a_1341_, 1);
lean_inc(v_levelParams_1345_);
v_type_1346_ = lean_ctor_get(v_a_1341_, 2);
lean_inc_ref(v_type_1346_);
lean_dec(v_a_1341_);
v___x_1347_ = l_List_lengthTR___redArg(v_levelParams_1345_);
v___x_1348_ = l_List_lengthTR___redArg(v_us_1334_);
v___x_1349_ = lean_nat_dec_eq(v___x_1347_, v___x_1348_);
lean_dec(v___x_1348_);
lean_dec(v___x_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref(v_type_1346_);
lean_dec(v_levelParams_1345_);
lean_del_object(v___x_1343_);
v___x_1350_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1333_, v_us_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_dec(v_c_1333_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_levelParams_1345_);
lean_ctor_set(v___x_1351_, 1, v_us_1334_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_type_1346_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1352_);
v___x_1354_ = v___x_1343_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_us_1334_);
lean_dec(v_c_1333_);
v_a_1357_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1340_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1340_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy___boxed(lean_object* v_c_1365_, lean_object* v_us_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_c_1365_, v_us_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
return v_res_1372_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1379_, lean_object* v_idx_1380_, lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v_00_u03b1_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1390_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1391_ = l_Lean_mkProj(v_structName_1379_, v_idx_1380_, v_e_1381_);
v___x_1392_ = l_Lean_indentExpr(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1390_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = l_Lean_indentExpr(v_a_1382_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1397_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1399_, lean_object* v_idx_1400_, lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v_00_u03b1_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1399_, v_idx_1400_, v_e_1401_, v_a_1402_, v_00_u03b1_1403_, v_x_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v_env_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_st_ref_get(v___y_1415_);
v_env_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1418_);
lean_dec(v___x_1417_);
v___x_1419_ = 0;
lean_inc(v_constName_1411_);
v___x_1420_ = l_Lean_Environment_find_x3f(v_env_1418_, v_constName_1411_, v___x_1419_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1421_;
}
else
{
lean_object* v_val_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_constName_1411_);
v_val_1422_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1420_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_val_1422_);
lean_dec(v___x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 0);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_val_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1437_, lean_object* v_structName_1438_, lean_object* v_e_1439_, lean_object* v_idx_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_a_1450_; uint8_t v___x_1454_; 
v___x_1454_ = lean_nat_dec_lt(v_a_1442_, v_upperBound_1437_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_idx_1440_);
lean_dec_ref(v_e_1439_);
lean_dec(v_structName_1438_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1443_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; 
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
v___x_1456_ = lean_whnf(v_b_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
if (lean_obj_tag(v_a_1457_) == 7)
{
lean_object* v_body_1458_; uint8_t v___x_1459_; 
v_body_1458_ = lean_ctor_get(v_a_1457_, 2);
lean_inc_ref(v_body_1458_);
lean_dec_ref_known(v_a_1457_, 3);
v___x_1459_ = l_Lean_Expr_hasLooseBVars(v_body_1458_);
if (v___x_1459_ == 0)
{
v_a_1450_ = v_body_1458_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v_e_1439_);
lean_inc(v_a_1442_);
lean_inc(v_structName_1438_);
v___x_1460_ = l_Lean_mkProj(v_structName_1438_, v_a_1442_, v_e_1439_);
v___x_1461_ = lean_expr_instantiate1(v_body_1458_, v___x_1460_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v_body_1458_);
v_a_1450_ = v___x_1461_;
goto v___jp_1449_;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1462_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1439_);
lean_inc(v_idx_1440_);
lean_inc(v_structName_1438_);
v___x_1463_ = l_Lean_mkProj(v_structName_1438_, v_idx_1440_, v_e_1439_);
v___x_1464_ = l_Lean_indentExpr(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1462_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
lean_inc_ref(v_a_1441_);
v___x_1468_ = l_Lean_indentExpr(v_a_1441_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1469_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v_a_1450_ = v_a_1457_;
goto v___jp_1449_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1457_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_idx_1440_);
lean_dec_ref(v_e_1439_);
lean_dec(v_structName_1438_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_idx_1440_);
lean_dec_ref(v_e_1439_);
lean_dec(v_structName_1438_);
return v___x_1456_;
}
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v_a_1442_, v___x_1451_);
lean_dec(v_a_1442_);
v_a_1442_ = v___x_1452_;
v_b_1443_ = v_a_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1479_, lean_object* v_structName_1480_, lean_object* v_e_1481_, lean_object* v_idx_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1479_, v_structName_1480_, v_e_1481_, v_idx_1482_, v_a_1483_, v_a_1484_, v_b_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v_upperBound_1479_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1492_, lean_object* v_structName_1493_, lean_object* v_e_1494_, lean_object* v_idx_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_a_1505_; uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_lt(v_a_1497_, v_upperBound_1492_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_idx_1495_);
lean_dec_ref(v_e_1494_);
lean_dec(v_structName_1493_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_b_1498_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
v___x_1511_ = lean_whnf(v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
if (lean_obj_tag(v_a_1512_) == 7)
{
lean_object* v_body_1513_; uint8_t v___x_1514_; 
v_body_1513_ = lean_ctor_get(v_a_1512_, 2);
lean_inc_ref(v_body_1513_);
lean_dec_ref_known(v_a_1512_, 3);
v___x_1514_ = l_Lean_Expr_hasLooseBVars(v_body_1513_);
if (v___x_1514_ == 0)
{
v_a_1505_ = v_body_1513_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v_e_1494_);
lean_inc(v_a_1497_);
lean_inc(v_structName_1493_);
v___x_1515_ = l_Lean_mkProj(v_structName_1493_, v_a_1497_, v_e_1494_);
v___x_1516_ = lean_expr_instantiate1(v_body_1513_, v___x_1515_);
lean_dec_ref(v___x_1515_);
lean_dec_ref(v_body_1513_);
v_a_1505_ = v___x_1516_;
goto v___jp_1504_;
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1517_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1494_);
lean_inc(v_idx_1495_);
lean_inc(v_structName_1493_);
v___x_1518_ = l_Lean_mkProj(v_structName_1493_, v_idx_1495_, v_e_1494_);
v___x_1519_ = l_Lean_indentExpr(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1517_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_inc_ref(v_a_1496_);
v___x_1523_ = l_Lean_indentExpr(v_a_1496_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1524_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_dec_ref_known(v___x_1525_, 1);
v_a_1505_ = v_a_1512_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1512_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_idx_1495_);
lean_dec_ref(v_e_1494_);
lean_dec(v_structName_1493_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_idx_1495_);
lean_dec_ref(v_e_1494_);
lean_dec(v_structName_1493_);
return v___x_1511_;
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_a_1497_, v___x_1506_);
lean_dec(v_a_1497_);
v___x_1508_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1492_, v_structName_1493_, v_e_1494_, v_idx_1495_, v_a_1496_, v___x_1507_, v_a_1505_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1534_, lean_object* v_structName_1535_, lean_object* v_e_1536_, lean_object* v_idx_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1534_, v_structName_1535_, v_e_1536_, v_idx_1537_, v_a_1538_, v_a_1539_, v_b_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_upperBound_1534_);
return v_res_1546_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1547_; lean_object* v_dummy_1548_; 
v___x_1547_ = lean_box(0);
v_dummy_1548_ = l_Lean_Expr_sort___override(v___x_1547_);
return v_dummy_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1549_, lean_object* v_idx_1550_, lean_object* v_e_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
lean_inc_ref(v_e_1551_);
v___x_1557_ = lean_infer_type(v_e_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
lean_inc(v_a_1555_);
lean_inc_ref(v_a_1554_);
lean_inc(v_a_1553_);
lean_inc_ref(v_a_1552_);
v___x_1559_ = lean_whnf(v_a_1558_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = l_Lean_Expr_getAppFn(v_a_1560_);
if (lean_obj_tag(v___x_1561_) == 4)
{
lean_object* v_declName_1562_; lean_object* v_us_1563_; lean_object* v___x_1564_; lean_object* v_env_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; 
v_declName_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_declName_1562_);
v_us_1563_ = lean_ctor_get(v___x_1561_, 1);
lean_inc(v_us_1563_);
lean_dec_ref_known(v___x_1561_, 2);
v___x_1564_ = lean_st_ref_get(v_a_1555_);
v_env_1568_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1568_);
lean_dec(v___x_1564_);
v___x_1569_ = 0;
v___x_1570_ = l_Lean_Environment_find_x3f(v_env_1568_, v_declName_1562_, v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_us_1563_);
v___x_1571_ = lean_box(0);
v___x_1572_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1571_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1572_;
}
else
{
lean_object* v_val_1573_; 
v_val_1573_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v___x_1570_, 1);
if (lean_obj_tag(v_val_1573_) == 5)
{
lean_object* v_val_1574_; lean_object* v_ctors_1575_; 
v_val_1574_ = lean_ctor_get(v_val_1573_, 0);
lean_inc_ref(v_val_1574_);
lean_dec_ref_known(v_val_1573_, 1);
v_ctors_1575_ = lean_ctor_get(v_val_1574_, 4);
lean_inc(v_ctors_1575_);
if (lean_obj_tag(v_ctors_1575_) == 1)
{
lean_object* v_tail_1576_; 
v_tail_1576_ = lean_ctor_get(v_ctors_1575_, 1);
if (lean_obj_tag(v_tail_1576_) == 0)
{
lean_object* v_toConstantVal_1577_; lean_object* v_numParams_1578_; lean_object* v_numIndices_1579_; lean_object* v_head_1580_; lean_object* v___x_1581_; 
v_toConstantVal_1577_ = lean_ctor_get(v_val_1574_, 0);
lean_inc_ref(v_toConstantVal_1577_);
v_numParams_1578_ = lean_ctor_get(v_val_1574_, 1);
lean_inc(v_numParams_1578_);
v_numIndices_1579_ = lean_ctor_get(v_val_1574_, 2);
lean_inc(v_numIndices_1579_);
lean_dec_ref(v_val_1574_);
v_head_1580_ = lean_ctor_get(v_ctors_1575_, 0);
lean_inc(v_head_1580_);
lean_dec_ref_known(v_ctors_1575_, 2);
v___x_1581_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1580_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
if (lean_obj_tag(v_a_1582_) == 6)
{
lean_object* v_val_1583_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v_name_1623_; uint8_t v___x_1624_; 
v_val_1583_ = lean_ctor_get(v_a_1582_, 0);
lean_inc_ref(v_val_1583_);
lean_dec_ref_known(v_a_1582_, 1);
v_name_1623_ = lean_ctor_get(v_toConstantVal_1577_, 0);
lean_inc(v_name_1623_);
lean_dec_ref(v_toConstantVal_1577_);
v___x_1624_ = lean_name_eq(v_name_1623_, v_structName_1549_);
lean_dec(v_name_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_val_1583_);
lean_dec(v_numIndices_1579_);
lean_dec(v_numParams_1578_);
lean_dec(v_us_1563_);
v___x_1625_ = lean_box(0);
v___x_1626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1625_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
v___y_1585_ = v_a_1552_;
v___y_1586_ = v_a_1553_;
v___y_1587_ = v_a_1554_;
v___y_1588_ = v_a_1555_;
goto v___jp_1584_;
}
v___jp_1584_:
{
lean_object* v_dummy_1589_; lean_object* v_nargs_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_dummy_1589_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1590_ = l_Lean_Expr_getAppNumArgs(v_a_1560_);
lean_inc(v_nargs_1590_);
v___x_1591_ = lean_mk_array(v_nargs_1590_, v_dummy_1589_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_sub(v_nargs_1590_, v___x_1592_);
lean_dec(v_nargs_1590_);
lean_inc(v_a_1560_);
v___x_1594_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1560_, v___x_1591_, v___x_1593_);
v___x_1595_ = lean_nat_add(v_numParams_1578_, v_numIndices_1579_);
lean_dec(v_numIndices_1579_);
v___x_1596_ = lean_array_get_size(v___x_1594_);
v___x_1597_ = lean_nat_dec_eq(v___x_1595_, v___x_1596_);
lean_dec(v___x_1595_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v___x_1594_);
lean_dec_ref(v_val_1583_);
lean_dec(v_numParams_1578_);
lean_dec(v_us_1563_);
v___x_1598_ = lean_box(0);
v___x_1599_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1598_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1599_;
}
else
{
lean_object* v_toConstantVal_1600_; lean_object* v_name_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_toConstantVal_1600_ = lean_ctor_get(v_val_1583_, 0);
lean_inc_ref(v_toConstantVal_1600_);
lean_dec_ref(v_val_1583_);
v_name_1601_ = lean_ctor_get(v_toConstantVal_1600_, 0);
lean_inc(v_name_1601_);
lean_dec_ref(v_toConstantVal_1600_);
v___x_1602_ = l_Lean_mkConst(v_name_1601_, v_us_1563_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = l_Array_toSubarray___redArg(v___x_1594_, v___x_1603_, v_numParams_1578_);
v___x_1605_ = l_Subarray_copy___redArg(v___x_1604_);
v___x_1606_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1602_, v___x_1605_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec_ref(v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
lean_inc(v_a_1560_);
lean_inc_ref(v_e_1551_);
lean_inc(v_structName_1549_);
lean_inc(v_idx_1550_);
v___x_1608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1550_, v_structName_1549_, v_e_1551_, v_idx_1550_, v_a_1560_, v___x_1603_, v_a_1607_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
v___x_1610_ = lean_whnf(v_a_1609_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1622_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1622_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1622_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
if (lean_obj_tag(v_a_1611_) == 7)
{
lean_object* v_binderType_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
v_binderType_1615_ = lean_ctor_get(v_a_1611_, 1);
lean_inc_ref(v_binderType_1615_);
lean_dec_ref_known(v_a_1611_, 3);
v___x_1616_ = lean_expr_consume_type_annotations(v_binderType_1615_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_del_object(v___x_1613_);
lean_dec(v_a_1611_);
v___x_1620_ = lean_box(0);
v___x_1621_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1620_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1621_;
}
}
}
else
{
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
return v___x_1610_;
}
}
else
{
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
return v___x_1608_;
}
}
else
{
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
return v___x_1606_;
}
}
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_a_1582_);
lean_dec(v_numIndices_1579_);
lean_dec(v_numParams_1578_);
lean_dec_ref(v_toConstantVal_1577_);
lean_dec(v_us_1563_);
v___x_1635_ = lean_box(0);
v___x_1636_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1635_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1636_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_numIndices_1579_);
lean_dec(v_numParams_1578_);
lean_dec_ref(v_toConstantVal_1577_);
lean_dec(v_us_1563_);
lean_dec(v_a_1560_);
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
v_a_1637_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1581_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1581_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1575_, 2);
lean_dec_ref(v_val_1574_);
lean_dec(v_us_1563_);
goto v___jp_1565_;
}
}
else
{
lean_dec(v_ctors_1575_);
lean_dec_ref(v_val_1574_);
lean_dec(v_us_1563_);
goto v___jp_1565_;
}
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_val_1573_);
lean_dec(v_us_1563_);
v___x_1645_ = lean_box(0);
v___x_1646_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1645_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1646_;
}
}
v___jp_1565_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1566_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1567_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v___x_1561_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1549_, v_idx_1550_, v_e_1551_, v_a_1560_, lean_box(0), v___x_1647_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1648_;
}
}
else
{
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
return v___x_1559_;
}
}
else
{
lean_dec_ref(v_e_1551_);
lean_dec(v_idx_1550_);
lean_dec(v_structName_1549_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1649_, lean_object* v_idx_1650_, lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1649_, v_idx_1650_, v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1658_, lean_object* v_structName_1659_, lean_object* v_e_1660_, lean_object* v_idx_1661_, lean_object* v_a_1662_, lean_object* v_inst_1663_, lean_object* v_R_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_, lean_object* v_c_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1658_, v_structName_1659_, v_e_1660_, v_idx_1661_, v_a_1662_, v_a_1665_, v_b_1666_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1674_, lean_object* v_structName_1675_, lean_object* v_e_1676_, lean_object* v_idx_1677_, lean_object* v_a_1678_, lean_object* v_inst_1679_, lean_object* v_R_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_, lean_object* v_c_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1674_, v_structName_1675_, v_e_1676_, v_idx_1677_, v_a_1678_, v_inst_1679_, v_R_1680_, v_a_1681_, v_b_1682_, v_c_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v_upperBound_1674_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1690_, lean_object* v_structName_1691_, lean_object* v_e_1692_, lean_object* v_idx_1693_, lean_object* v_a_1694_, lean_object* v_inst_1695_, lean_object* v_R_1696_, lean_object* v_a_1697_, lean_object* v_b_1698_, lean_object* v_c_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1690_, v_structName_1691_, v_e_1692_, v_idx_1693_, v_a_1694_, v_a_1697_, v_b_1698_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1706_, lean_object* v_structName_1707_, lean_object* v_e_1708_, lean_object* v_idx_1709_, lean_object* v_a_1710_, lean_object* v_inst_1711_, lean_object* v_R_1712_, lean_object* v_a_1713_, lean_object* v_b_1714_, lean_object* v_c_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1706_, v_structName_1707_, v_e_1708_, v_idx_1709_, v_a_1710_, v_inst_1711_, v_R_1712_, v_a_1713_, v_b_1714_, v_c_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v_upperBound_1706_);
return v_res_1721_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1724_ = l_Lean_stringToMessageData(v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1731_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1732_ = l_Lean_indentExpr(v_type_1725_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1733_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1742_, lean_object* v_type_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_type_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1750_, v_type_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v_ks_1762_; lean_object* v_vs_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1787_; 
v_ks_1762_ = lean_ctor_get(v_x_1758_, 0);
v_vs_1763_ = lean_ctor_get(v_x_1758_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_x_1758_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1765_ = v_x_1758_;
v_isShared_1766_ = v_isSharedCheck_1787_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_vs_1763_);
lean_inc(v_ks_1762_);
lean_dec(v_x_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1787_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_array_get_size(v_ks_1762_);
v___x_1768_ = lean_nat_dec_lt(v_x_1759_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_x_1759_);
v___x_1769_ = lean_array_push(v_ks_1762_, v_x_1760_);
v___x_1770_ = lean_array_push(v_vs_1763_, v_x_1761_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1770_);
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1772_ = v___x_1765_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
else
{
lean_object* v_k_x27_1774_; uint8_t v___x_1775_; 
v_k_x27_1774_ = lean_array_fget_borrowed(v_ks_1762_, v_x_1759_);
v___x_1775_ = l_Lean_instBEqMVarId_beq(v_x_1760_, v_k_x27_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1777_; 
if (v_isShared_1766_ == 0)
{
v___x_1777_ = v___x_1765_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_ks_1762_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_vs_1763_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_x_1759_, v___x_1778_);
lean_dec(v_x_1759_);
v_x_1758_ = v___x_1777_;
v_x_1759_ = v___x_1779_;
goto _start;
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_array_fset(v_ks_1762_, v_x_1759_, v_x_1760_);
v___x_1783_ = lean_array_fset(v_vs_1763_, v_x_1759_, v_x_1761_);
lean_dec(v_x_1759_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1783_);
lean_ctor_set(v___x_1765_, 0, v___x_1782_);
v___x_1785_ = v___x_1765_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1783_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1788_, lean_object* v_k_1789_, lean_object* v_v_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1788_, v___x_1791_, v_k_1789_, v_v_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1794_, size_t v_x_1795_, size_t v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v_es_1799_; size_t v___x_1800_; size_t v___x_1801_; lean_object* v_j_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_es_1799_ = lean_ctor_get(v_x_1794_, 0);
v___x_1800_ = ((size_t)31ULL);
v___x_1801_ = lean_usize_land(v_x_1795_, v___x_1800_);
v_j_1802_ = lean_usize_to_nat(v___x_1801_);
v___x_1803_ = lean_array_get_size(v_es_1799_);
v___x_1804_ = lean_nat_dec_lt(v_j_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec(v_j_1802_);
lean_dec(v_x_1798_);
lean_dec(v_x_1797_);
return v_x_1794_;
}
else
{
lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1843_; 
lean_inc_ref(v_es_1799_);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_x_1794_, 0);
lean_dec(v_unused_1844_);
v___x_1806_ = v_x_1794_;
v_isShared_1807_ = v_isSharedCheck_1843_;
goto v_resetjp_1805_;
}
else
{
lean_dec(v_x_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1843_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v_xs_x27_1810_; lean_object* v___y_1812_; 
v_v_1808_ = lean_array_fget(v_es_1799_, v_j_1802_);
v___x_1809_ = lean_box(0);
v_xs_x27_1810_ = lean_array_fset(v_es_1799_, v_j_1802_, v___x_1809_);
switch(lean_obj_tag(v_v_1808_))
{
case 0:
{
lean_object* v_key_1817_; lean_object* v_val_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_key_1817_ = lean_ctor_get(v_v_1808_, 0);
v_val_1818_ = lean_ctor_get(v_v_1808_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_v_1808_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1820_ = v_v_1808_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_val_1818_);
lean_inc(v_key_1817_);
lean_dec(v_v_1808_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Lean_instBEqMVarId_beq(v_x_1797_, v_key_1817_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_del_object(v___x_1820_);
v___x_1823_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1817_, v_val_1818_, v_x_1797_, v_x_1798_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
v___y_1812_ = v___x_1824_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1826_; 
lean_dec(v_val_1818_);
lean_dec(v_key_1817_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v_x_1798_);
lean_ctor_set(v___x_1820_, 0, v_x_1797_);
v___x_1826_ = v___x_1820_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_x_1797_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_x_1798_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1812_ = v___x_1826_;
goto v___jp_1811_;
}
}
}
}
case 1:
{
lean_object* v_node_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1841_; 
v_node_1829_ = lean_ctor_get(v_v_1808_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_v_1808_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1831_ = v_v_1808_;
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_node_1829_);
lean_dec(v_v_1808_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
size_t v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1833_ = ((size_t)5ULL);
v___x_1834_ = lean_usize_shift_right(v_x_1795_, v___x_1833_);
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_x_1796_, v___x_1835_);
v___x_1837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1829_, v___x_1834_, v___x_1836_, v_x_1797_, v_x_1798_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1812_ = v___x_1839_;
goto v___jp_1811_;
}
}
}
default: 
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_x_1797_);
lean_ctor_set(v___x_1842_, 1, v_x_1798_);
v___y_1812_ = v___x_1842_;
goto v___jp_1811_;
}
}
v___jp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_array_fset(v_xs_x27_1810_, v_j_1802_, v___y_1812_);
lean_dec(v_j_1802_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1813_);
v___x_1815_ = v___x_1806_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
else
{
lean_object* v_ks_1845_; lean_object* v_vs_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1864_; 
v_ks_1845_ = lean_ctor_get(v_x_1794_, 0);
v_vs_1846_ = lean_ctor_get(v_x_1794_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1848_ = v_x_1794_;
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_vs_1846_);
lean_inc(v_ks_1845_);
lean_dec(v_x_1794_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1864_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_ks_1845_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_vs_1846_);
v___x_1851_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v_newNode_1852_; size_t v___x_1853_; uint8_t v___x_1854_; 
v_newNode_1852_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1851_, v_x_1797_, v_x_1798_);
v___x_1853_ = ((size_t)7ULL);
v___x_1854_ = lean_usize_dec_le(v___x_1853_, v_x_1796_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1852_);
v___x_1856_ = lean_unsigned_to_nat(4u);
v___x_1857_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
lean_dec(v___x_1855_);
if (v___x_1857_ == 0)
{
lean_object* v_ks_1858_; lean_object* v_vs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_ks_1858_ = lean_ctor_get(v_newNode_1852_, 0);
lean_inc_ref(v_ks_1858_);
v_vs_1859_ = lean_ctor_get(v_newNode_1852_, 1);
lean_inc_ref(v_vs_1859_);
lean_dec_ref(v_newNode_1852_);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1796_, v_ks_1858_, v_vs_1859_, v___x_1860_, v___x_1861_);
lean_dec_ref(v_vs_1859_);
lean_dec_ref(v_ks_1858_);
return v___x_1862_;
}
else
{
return v_newNode_1852_;
}
}
else
{
return v_newNode_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1865_, lean_object* v_keys_1866_, lean_object* v_vals_1867_, lean_object* v_i_1868_, lean_object* v_entries_1869_){
_start:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_array_get_size(v_keys_1866_);
v___x_1871_ = lean_nat_dec_lt(v_i_1868_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v_i_1868_);
return v_entries_1869_;
}
else
{
lean_object* v_k_1872_; lean_object* v_v_1873_; uint64_t v___x_1874_; size_t v_h_1875_; size_t v___x_1876_; lean_object* v___x_1877_; size_t v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; size_t v_h_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_k_1872_ = lean_array_fget_borrowed(v_keys_1866_, v_i_1868_);
v_v_1873_ = lean_array_fget_borrowed(v_vals_1867_, v_i_1868_);
v___x_1874_ = l_Lean_instHashableMVarId_hash(v_k_1872_);
v_h_1875_ = lean_uint64_to_usize(v___x_1874_);
v___x_1876_ = ((size_t)5ULL);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = ((size_t)1ULL);
v___x_1879_ = lean_usize_sub(v_depth_1865_, v___x_1878_);
v___x_1880_ = lean_usize_mul(v___x_1876_, v___x_1879_);
v_h_1881_ = lean_usize_shift_right(v_h_1875_, v___x_1880_);
v___x_1882_ = lean_nat_add(v_i_1868_, v___x_1877_);
lean_dec(v_i_1868_);
lean_inc(v_v_1873_);
lean_inc(v_k_1872_);
v___x_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1869_, v_h_1881_, v_depth_1865_, v_k_1872_, v_v_1873_);
v_i_1868_ = v___x_1882_;
v_entries_1869_ = v___x_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1885_, lean_object* v_keys_1886_, lean_object* v_vals_1887_, lean_object* v_i_1888_, lean_object* v_entries_1889_){
_start:
{
size_t v_depth_boxed_1890_; lean_object* v_res_1891_; 
v_depth_boxed_1890_ = lean_unbox_usize(v_depth_1885_);
lean_dec(v_depth_1885_);
v_res_1891_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1890_, v_keys_1886_, v_vals_1887_, v_i_1888_, v_entries_1889_);
lean_dec_ref(v_vals_1887_);
lean_dec_ref(v_keys_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
size_t v_x_1155__boxed_1897_; size_t v_x_1156__boxed_1898_; lean_object* v_res_1899_; 
v_x_1155__boxed_1897_ = lean_unbox_usize(v_x_1893_);
lean_dec(v_x_1893_);
v_x_1156__boxed_1898_ = lean_unbox_usize(v_x_1894_);
lean_dec(v_x_1894_);
v_res_1899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1892_, v_x_1155__boxed_1897_, v_x_1156__boxed_1898_, v_x_1895_, v_x_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_){
_start:
{
uint64_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = l_Lean_instHashableMVarId_hash(v_x_1901_);
v___x_1904_ = lean_uint64_to_usize(v___x_1903_);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1900_, v___x_1904_, v___x_1905_, v_x_1901_, v_x_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1907_, lean_object* v_val_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v_mctx_1912_; lean_object* v_cache_1913_; lean_object* v_zetaDeltaFVarIds_1914_; lean_object* v_postponed_1915_; lean_object* v_diag_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1946_; 
v___x_1911_ = lean_st_ref_take(v___y_1909_);
v_mctx_1912_ = lean_ctor_get(v___x_1911_, 0);
v_cache_1913_ = lean_ctor_get(v___x_1911_, 1);
v_zetaDeltaFVarIds_1914_ = lean_ctor_get(v___x_1911_, 2);
v_postponed_1915_ = lean_ctor_get(v___x_1911_, 3);
v_diag_1916_ = lean_ctor_get(v___x_1911_, 4);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1918_ = v___x_1911_;
v_isShared_1919_ = v_isSharedCheck_1946_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_diag_1916_);
lean_inc(v_postponed_1915_);
lean_inc(v_zetaDeltaFVarIds_1914_);
lean_inc(v_cache_1913_);
lean_inc(v_mctx_1912_);
lean_dec(v___x_1911_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1946_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_depth_1920_; lean_object* v_levelAssignDepth_1921_; lean_object* v_lmvarCounter_1922_; lean_object* v_mvarCounter_1923_; lean_object* v_lDecls_1924_; lean_object* v_decls_1925_; lean_object* v_userNames_1926_; lean_object* v_lAssignment_1927_; lean_object* v_eAssignment_1928_; lean_object* v_dAssignment_1929_; lean_object* v_instanceTypedMVars_1930_; lean_object* v_synthNormMemo_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1945_; 
v_depth_1920_ = lean_ctor_get(v_mctx_1912_, 0);
v_levelAssignDepth_1921_ = lean_ctor_get(v_mctx_1912_, 1);
v_lmvarCounter_1922_ = lean_ctor_get(v_mctx_1912_, 2);
v_mvarCounter_1923_ = lean_ctor_get(v_mctx_1912_, 3);
v_lDecls_1924_ = lean_ctor_get(v_mctx_1912_, 4);
v_decls_1925_ = lean_ctor_get(v_mctx_1912_, 5);
v_userNames_1926_ = lean_ctor_get(v_mctx_1912_, 6);
v_lAssignment_1927_ = lean_ctor_get(v_mctx_1912_, 7);
v_eAssignment_1928_ = lean_ctor_get(v_mctx_1912_, 8);
v_dAssignment_1929_ = lean_ctor_get(v_mctx_1912_, 9);
v_instanceTypedMVars_1930_ = lean_ctor_get(v_mctx_1912_, 10);
v_synthNormMemo_1931_ = lean_ctor_get(v_mctx_1912_, 11);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_mctx_1912_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1933_ = v_mctx_1912_;
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_synthNormMemo_1931_);
lean_inc(v_instanceTypedMVars_1930_);
lean_inc(v_dAssignment_1929_);
lean_inc(v_eAssignment_1928_);
lean_inc(v_lAssignment_1927_);
lean_inc(v_userNames_1926_);
lean_inc(v_decls_1925_);
lean_inc(v_lDecls_1924_);
lean_inc(v_mvarCounter_1923_);
lean_inc(v_lmvarCounter_1922_);
lean_inc(v_levelAssignDepth_1921_);
lean_inc(v_depth_1920_);
lean_dec(v_mctx_1912_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1928_, v_mvarId_1907_, v_val_1908_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 8, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_depth_1920_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_levelAssignDepth_1921_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_lmvarCounter_1922_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_mvarCounter_1923_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_lDecls_1924_);
lean_ctor_set(v_reuseFailAlloc_1944_, 5, v_decls_1925_);
lean_ctor_set(v_reuseFailAlloc_1944_, 6, v_userNames_1926_);
lean_ctor_set(v_reuseFailAlloc_1944_, 7, v_lAssignment_1927_);
lean_ctor_set(v_reuseFailAlloc_1944_, 8, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1944_, 9, v_dAssignment_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 10, v_instanceTypedMVars_1930_);
lean_ctor_set(v_reuseFailAlloc_1944_, 11, v_synthNormMemo_1931_);
v___x_1938_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1938_);
v___x_1940_ = v___x_1918_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_cache_1913_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_zetaDeltaFVarIds_1914_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_postponed_1915_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_diag_1916_);
v___x_1940_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_st_ref_put(v___y_1909_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1935_);
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1947_, lean_object* v_val_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1947_, v_val_1948_, v___y_1949_);
lean_dec(v___y_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
lean_inc(v_a_1956_);
lean_inc_ref(v_a_1955_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc_ref(v_type_1952_);
v___x_1958_ = lean_infer_type(v_type_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Meta_whnfD(v_a_1959_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1995_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1995_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1995_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
switch(lean_obj_tag(v_a_1961_))
{
case 3:
{
lean_object* v_u_1965_; lean_object* v___x_1967_; 
lean_dec_ref(v_type_1952_);
v_u_1965_ = lean_ctor_get(v_a_1961_, 0);
lean_inc(v_u_1965_);
lean_dec_ref_known(v_a_1961_, 1);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_u_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_u_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
case 2:
{
lean_object* v_mvarId_1969_; lean_object* v___x_1970_; 
lean_del_object(v___x_1963_);
v_mvarId_1969_ = lean_ctor_get(v_a_1961_, 0);
lean_inc_n(v_mvarId_1969_, 2);
lean_dec_ref_known(v_a_1961_, 1);
v___x_1970_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1969_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; uint8_t v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = lean_unbox(v_a_1971_);
lean_dec(v_a_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref(v_type_1952_);
v___x_1973_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_n(v_a_1974_, 2);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_mkSort(v_a_1974_);
v___x_1976_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1969_, v___x_1975_, v_a_1954_);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v___x_1976_, 0);
lean_dec(v_unused_1984_);
v___x_1978_ = v___x_1976_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v___x_1976_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v_a_1974_);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1974_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_dec(v_mvarId_1969_);
return v___x_1973_;
}
}
else
{
lean_object* v___x_1985_; 
lean_dec(v_mvarId_1969_);
v___x_1985_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1985_;
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_mvarId_1969_);
lean_dec_ref(v_type_1952_);
v_a_1986_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1970_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1970_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
default: 
{
lean_object* v___x_1994_; 
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
v___x_1994_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_type_1952_);
v_a_1996_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1960_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1960_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_type_1952_);
v_a_2004_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1958_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1958_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_getLevel(v_type_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2019_, lean_object* v_val_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2019_, v_val_2020_, v___y_2022_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2027_, lean_object* v_val_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2027_, v_val_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2036_, v_x_2037_, v_x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, size_t v_x_2042_, size_t v_x_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2041_, v_x_2042_, v_x_2043_, v_x_2044_, v_x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
size_t v_x_1504__boxed_2053_; size_t v_x_1505__boxed_2054_; lean_object* v_res_2055_; 
v_x_1504__boxed_2053_ = lean_unbox_usize(v_x_2049_);
lean_dec(v_x_2049_);
v_x_1505__boxed_2054_ = lean_unbox_usize(v_x_2050_);
lean_dec(v_x_2050_);
v_res_2055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2047_, v_x_2048_, v_x_1504__boxed_2053_, v_x_1505__boxed_2054_, v_x_2051_, v_x_2052_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2056_, lean_object* v_n_2057_, lean_object* v_k_2058_, lean_object* v_v_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2057_, v_k_2058_, v_v_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2061_, size_t v_depth_2062_, lean_object* v_keys_2063_, lean_object* v_vals_2064_, lean_object* v_heq_2065_, lean_object* v_i_2066_, lean_object* v_entries_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2062_, v_keys_2063_, v_vals_2064_, v_i_2066_, v_entries_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2069_, lean_object* v_depth_2070_, lean_object* v_keys_2071_, lean_object* v_vals_2072_, lean_object* v_heq_2073_, lean_object* v_i_2074_, lean_object* v_entries_2075_){
_start:
{
size_t v_depth_boxed_2076_; lean_object* v_res_2077_; 
v_depth_boxed_2076_ = lean_unbox_usize(v_depth_2070_);
lean_dec(v_depth_2070_);
v_res_2077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2069_, v_depth_boxed_2076_, v_keys_2071_, v_vals_2072_, v_heq_2073_, v_i_2074_, v_entries_2075_);
lean_dec_ref(v_vals_2072_);
lean_dec_ref(v_keys_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2079_, v_x_2080_, v_x_2081_, v_x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2084_, lean_object* v_b_2085_, lean_object* v_c_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
lean_inc(v___y_2090_);
lean_inc_ref(v___y_2089_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
v___x_2092_ = lean_apply_7(v_k_2084_, v_b_2085_, v_c_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, lean_box(0));
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2093_, lean_object* v_b_2094_, lean_object* v_c_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2093_, v_b_2094_, v_c_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2102_, lean_object* v_k_2103_, uint8_t v_cleanupAnnotations_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___f_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___f_2110_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2110_, 0, v_k_2103_);
v___x_2111_ = 0;
v___x_2112_ = lean_box(0);
v___x_2113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2111_, v___x_2112_, v_type_2102_, v___f_2110_, v_cleanupAnnotations_2104_, v___x_2111_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_a_2122_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2130_, lean_object* v_k_2131_, lean_object* v_cleanupAnnotations_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2138_; lean_object* v_res_2139_; 
v_cleanupAnnotations_boxed_2138_ = lean_unbox(v_cleanupAnnotations_2132_);
v_res_2139_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2130_, v_k_2131_, v_cleanupAnnotations_boxed_2138_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2140_, lean_object* v_type_2141_, lean_object* v_k_2142_, uint8_t v_cleanupAnnotations_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2141_, v_k_2142_, v_cleanupAnnotations_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2150_, lean_object* v_type_2151_, lean_object* v_k_2152_, lean_object* v_cleanupAnnotations_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2159_; lean_object* v_res_2160_; 
v_cleanupAnnotations_boxed_2159_ = lean_unbox(v_cleanupAnnotations_2153_);
v_res_2160_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2150_, v_type_2151_, v_k_2152_, v_cleanupAnnotations_boxed_2159_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2161_, size_t v_i_2162_, size_t v_stop_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_eq(v_i_2162_, v_stop_2163_);
if (v___x_2170_ == 0)
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_sub(v_i_2162_, v___x_2171_);
v___x_2173_ = lean_array_uget_borrowed(v_as_2161_, v___x_2172_);
lean_inc(v___y_2168_);
lean_inc_ref(v___y_2167_);
lean_inc(v___y_2166_);
lean_inc_ref(v___y_2165_);
lean_inc(v___x_2173_);
v___x_2174_ = lean_infer_type(v___x_2173_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l_Lean_Meta_getLevel(v_a_2175_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_mkLevelIMax_x27(v_a_2177_, v_b_2164_);
v_i_2162_ = v___x_2172_;
v_b_2164_ = v___x_2178_;
goto _start;
}
else
{
lean_dec(v_b_2164_);
return v___x_2176_;
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_b_2164_);
v_a_2180_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2174_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2174_);
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
else
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_b_2164_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2189_, lean_object* v_i_2190_, lean_object* v_stop_2191_, lean_object* v_b_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
size_t v_i_boxed_2198_; size_t v_stop_boxed_2199_; lean_object* v_res_2200_; 
v_i_boxed_2198_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_stop_boxed_2199_ = lean_unbox_usize(v_stop_2191_);
lean_dec(v_stop_2191_);
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2189_, v_i_boxed_2198_, v_stop_boxed_2199_, v_b_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_as_2189_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2201_, lean_object* v_e_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_a_2209_; lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Meta_getLevel(v_e_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = lean_array_get_size(v_xs_2201_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = lean_nat_dec_lt(v___x_2216_, v___x_2215_);
if (v___x_2217_ == 0)
{
v_a_2209_ = v_a_2214_;
goto v___jp_2208_;
}
else
{
size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_usize_of_nat(v___x_2215_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2201_, v___x_2218_, v___x_2219_, v_a_2214_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v_a_2209_ = v_a_2221_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2213_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2213_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = l_Lean_Level_normalize(v_a_2209_);
lean_dec(v_a_2209_);
v___x_2211_ = l_Lean_mkSort(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2238_, lean_object* v_e_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2238_, v_e_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_xs_2238_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___f_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; 
v___f_2253_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2254_ = 0;
v___x_2255_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2247_, v___f_2253_, v___x_2254_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2263_, lean_object* v_k_2264_, uint8_t v_cleanupAnnotations_2265_, uint8_t v_preserveNondepLet_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___f_2272_; uint8_t v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2272_, 0, v_k_2264_);
v___x_2273_ = 1;
v___x_2274_ = 0;
v___x_2275_ = lean_box(0);
v___x_2276_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2263_, v___x_2273_, v___x_2273_, v_preserveNondepLet_2266_, v___x_2274_, v___x_2275_, v___f_2272_, v_cleanupAnnotations_2265_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_a_2285_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2276_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2276_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2293_, lean_object* v_k_2294_, lean_object* v_cleanupAnnotations_2295_, lean_object* v_preserveNondepLet_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2302_; uint8_t v_preserveNondepLet_boxed_2303_; lean_object* v_res_2304_; 
v_cleanupAnnotations_boxed_2302_ = lean_unbox(v_cleanupAnnotations_2295_);
v_preserveNondepLet_boxed_2303_ = lean_unbox(v_preserveNondepLet_2296_);
v_res_2304_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2293_, v_k_2294_, v_cleanupAnnotations_boxed_2302_, v_preserveNondepLet_boxed_2303_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2305_, lean_object* v_e_2306_, lean_object* v_k_2307_, uint8_t v_cleanupAnnotations_2308_, uint8_t v_preserveNondepLet_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2306_, v_k_2307_, v_cleanupAnnotations_2308_, v_preserveNondepLet_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_e_2317_, lean_object* v_k_2318_, lean_object* v_cleanupAnnotations_2319_, lean_object* v_preserveNondepLet_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2326_; uint8_t v_preserveNondepLet_boxed_2327_; lean_object* v_res_2328_; 
v_cleanupAnnotations_boxed_2326_ = lean_unbox(v_cleanupAnnotations_2319_);
v_preserveNondepLet_boxed_2327_ = lean_unbox(v_preserveNondepLet_2320_);
v_res_2328_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2316_, v_e_2317_, v_k_2318_, v_cleanupAnnotations_boxed_2326_, v_preserveNondepLet_boxed_2327_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2329_, lean_object* v_e_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
v___x_2336_ = lean_infer_type(v_e_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = 0;
v___x_2339_ = 1;
v___x_2340_ = 1;
v___x_2341_ = l_Lean_Meta_mkForallFVars(v_xs_2329_, v_a_2337_, v___x_2338_, v___x_2339_, v___x_2338_, v___x_2340_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2341_;
}
else
{
return v___x_2336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2342_, lean_object* v_e_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2342_, v_e_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_xs_2342_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___f_2357_; uint8_t v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v___f_2357_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2358_ = 0;
v___x_2359_ = 1;
v___x_2360_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2351_, v___f_2357_, v___x_2358_, v___x_2359_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2367_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2380_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2381_ = l_Lean_MessageData_ofName(v_mvarId_2374_);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2384_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2393_, lean_object* v_mvarId_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_mvarId_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2401_, v_mvarId_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_mctx_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_st_ref_get(v_a_2411_);
v_mctx_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_mctx_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2416_, v_mvarId_2409_);
lean_dec_ref(v_mctx_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2418_;
}
else
{
lean_object* v_val_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_mvarId_2409_);
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
lean_object* v_type_2423_; lean_object* v___x_2425_; 
v_type_2423_ = lean_ctor_get(v_val_2419_, 2);
lean_inc_ref(v_type_2423_);
lean_dec(v_val_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 0);
lean_ctor_set(v___x_2421_, 0, v_type_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_type_2423_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_lctx_2440_; lean_object* v___x_2441_; 
v_lctx_2440_ = lean_ctor_get(v_a_2436_, 2);
lean_inc(v_fvarId_2435_);
lean_inc_ref(v_lctx_2440_);
v___x_2441_ = lean_local_ctx_find(v_lctx_2440_, v_fvarId_2435_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2435_, v_a_2437_, v_a_2438_);
return v___x_2442_;
}
else
{
lean_object* v_val_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_fvarId_2435_);
v_val_2443_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2441_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_val_2443_);
lean_dec(v___x_2441_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = l_Lean_LocalDecl_type(v_val_2443_);
lean_dec(v_val_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec_ref(v_a_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2458_, v_a_2459_, v_a_2461_, v_a_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2471_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_instMonadEIO___redArg();
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2474_ = l_StateRefT_x27_instMonad___redArg(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_instMonadExceptOfEIO___redArg();
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___f_2479_; 
v___x_2478_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2479_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2479_, 0, v___x_2478_);
return v___f_2479_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___f_2481_; 
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2481_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2481_, 0, v___x_2480_);
return v___f_2481_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; 
v___f_2482_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2483_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___f_2483_);
lean_ctor_set(v___x_2484_, 1, v___f_2482_);
return v___x_2484_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___f_2486_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2486_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2486_, 0, v___x_2485_);
return v___f_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___f_2488_; 
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2488_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2488_, 0, v___x_2487_);
return v___f_2488_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
v___f_2489_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2490_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___f_2490_);
lean_ctor_set(v___x_2491_, 1, v___f_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2494_, lean_object* v_inferType_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
uint8_t v_cacheInferType_2540_; 
v_cacheInferType_2540_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2540_ == 0)
{
lean_dec_ref(v_e_2494_);
goto v___jp_2501_;
}
else
{
uint8_t v___x_2541_; 
v___x_2541_ = l_Lean_Expr_hasMVar(v_e_2494_);
if (v___x_2541_ == 0)
{
lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___f_2542_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2544_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2494_, v_a_2496_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2643_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2643_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2643_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2590_; lean_object* v_cache_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2638_; 
v___x_2590_ = lean_st_ref_get(v_a_2497_);
v_cache_2591_ = lean_ctor_get(v___x_2590_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; 
v_unused_2639_ = lean_ctor_get(v___x_2590_, 4);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v___x_2590_, 3);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v___x_2590_, 2);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2642_);
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2638_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_cache_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2638_;
goto v_resetjp_2592_;
}
v___jp_2549_:
{
lean_object* v___x_2550_; 
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_a_2497_);
lean_inc_ref(v_a_2496_);
v___x_2550_ = lean_apply_5(v_inferType_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, lean_box(0));
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; uint8_t v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
v___x_2552_ = l_Lean_Expr_hasMVar(v_a_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2588_; 
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2589_);
v___x_2554_ = v___x_2550_;
v_isShared_2555_ = v_isSharedCheck_2588_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2550_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2588_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v_cache_2557_; lean_object* v_mctx_2558_; lean_object* v_zetaDeltaFVarIds_2559_; lean_object* v_postponed_2560_; lean_object* v_diag_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2587_; 
v___x_2556_ = lean_st_ref_take(v_a_2497_);
v_cache_2557_ = lean_ctor_get(v___x_2556_, 1);
v_mctx_2558_ = lean_ctor_get(v___x_2556_, 0);
v_zetaDeltaFVarIds_2559_ = lean_ctor_get(v___x_2556_, 2);
v_postponed_2560_ = lean_ctor_get(v___x_2556_, 3);
v_diag_2561_ = lean_ctor_get(v___x_2556_, 4);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2563_ = v___x_2556_;
v_isShared_2564_ = v_isSharedCheck_2587_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_diag_2561_);
lean_inc(v_postponed_2560_);
lean_inc(v_zetaDeltaFVarIds_2559_);
lean_inc(v_cache_2557_);
lean_inc(v_mctx_2558_);
lean_dec(v___x_2556_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2587_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_inferType_2565_; lean_object* v_funInfo_2566_; lean_object* v_synthInstance_2567_; lean_object* v_whnf_2568_; lean_object* v_defEqTrans_2569_; lean_object* v_defEqPerm_2570_; lean_object* v_isUnitLike_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2586_; 
v_inferType_2565_ = lean_ctor_get(v_cache_2557_, 0);
v_funInfo_2566_ = lean_ctor_get(v_cache_2557_, 1);
v_synthInstance_2567_ = lean_ctor_get(v_cache_2557_, 2);
v_whnf_2568_ = lean_ctor_get(v_cache_2557_, 3);
v_defEqTrans_2569_ = lean_ctor_get(v_cache_2557_, 4);
v_defEqPerm_2570_ = lean_ctor_get(v_cache_2557_, 5);
v_isUnitLike_2571_ = lean_ctor_get(v_cache_2557_, 6);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_cache_2557_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2573_ = v_cache_2557_;
v_isShared_2574_ = v_isSharedCheck_2586_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_isUnitLike_2571_);
lean_inc(v_defEqPerm_2570_);
lean_inc(v_defEqTrans_2569_);
lean_inc(v_whnf_2568_);
lean_inc(v_synthInstance_2567_);
lean_inc(v_funInfo_2566_);
lean_inc(v_inferType_2565_);
lean_dec(v_cache_2557_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2586_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_inc(v_a_2551_);
v___x_2575_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2542_, v___x_2543_, v_inferType_2565_, v_a_2545_, v_a_2551_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_funInfo_2566_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_synthInstance_2567_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_whnf_2568_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_defEqTrans_2569_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v_defEqPerm_2570_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_isUnitLike_2571_);
v___x_2577_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v___x_2577_);
v___x_2579_ = v___x_2563_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_mctx_2558_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_zetaDeltaFVarIds_2559_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_postponed_2560_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_diag_2561_);
v___x_2579_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_st_ref_put(v_a_2497_, v___x_2579_);
if (v_isShared_2555_ == 0)
{
v___x_2582_ = v___x_2554_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2551_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2551_);
lean_dec(v_a_2545_);
return v___x_2550_;
}
}
else
{
lean_dec(v_a_2545_);
return v___x_2550_;
}
}
v_resetjp_2592_:
{
lean_object* v_inferType_2595_; lean_object* v___x_2596_; 
v_inferType_2595_ = lean_ctor_get(v_cache_2591_, 0);
lean_inc_ref(v_inferType_2595_);
lean_dec_ref(v_cache_2591_);
lean_inc(v_a_2545_);
v___x_2596_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2542_, v___x_2543_, v_inferType_2595_, v_a_2545_);
lean_dec_ref(v_inferType_2595_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; lean_object* v_toApplicative_2598_; lean_object* v_toFunctor_2599_; lean_object* v_toSeq_2600_; lean_object* v_toSeqLeft_2601_; lean_object* v_toSeqRight_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___x_2612_; 
lean_del_object(v___x_2547_);
v___x_2597_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2598_ = lean_ctor_get(v___x_2597_, 0);
v_toFunctor_2599_ = lean_ctor_get(v_toApplicative_2598_, 0);
v_toSeq_2600_ = lean_ctor_get(v_toApplicative_2598_, 2);
v_toSeqLeft_2601_ = lean_ctor_get(v_toApplicative_2598_, 3);
v_toSeqRight_2602_ = lean_ctor_get(v_toApplicative_2598_, 4);
v___f_2603_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2604_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2599_, 2);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toFunctor_2599_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toFunctor_2599_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___f_2605_);
lean_ctor_set(v___x_2607_, 1, v___f_2606_);
lean_inc(v_toSeqRight_2602_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeqRight_2602_);
lean_inc(v_toSeqLeft_2601_);
v___f_2609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2609_, 0, v_toSeqLeft_2601_);
lean_inc(v_toSeq_2600_);
v___f_2610_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2610_, 0, v_toSeq_2600_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 4, v___f_2608_);
lean_ctor_set(v___x_2593_, 3, v___f_2609_);
lean_ctor_set(v___x_2593_, 2, v___f_2610_);
lean_ctor_set(v___x_2593_, 1, v___f_2603_);
lean_ctor_set(v___x_2593_, 0, v___x_2607_);
v___x_2612_ = v___x_2593_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___f_2603_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v___f_2610_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v___f_2609_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v___f_2608_);
v___x_2612_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_toCold_2619_; lean_object* v_cancelTk_x3f_2620_; 
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___f_2604_);
v___x_2614_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2615_ = l_Lean_Core_instMonadRefCoreM;
v___x_2616_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2617_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2616_, v___x_2613_);
v___x_2618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2614_);
lean_ctor_set(v___x_2618_, 1, v___x_2615_);
lean_ctor_set(v___x_2618_, 2, v___x_2617_);
v_toCold_2619_ = lean_ctor_get(v_a_2498_, 0);
v_cancelTk_x3f_2620_ = lean_ctor_get(v_toCold_2619_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2620_) == 1)
{
lean_object* v_val_2621_; uint8_t v___x_2622_; 
v_val_2621_ = lean_ctor_get(v_cancelTk_x3f_2620_, 0);
v___x_2622_ = l_IO_CancelToken_isSet(v_val_2621_);
if (v___x_2622_ == 0)
{
lean_dec_ref_known(v___x_2618_, 3);
goto v___jp_2549_;
}
else
{
lean_object* v___x_2074__overap_2623_; lean_object* v___x_2624_; 
v___x_2074__overap_2623_ = l_Lean_throwInterruptException___redArg(v___x_2618_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
v___x_2624_ = lean_apply_3(v___x_2074__overap_2623_, v_a_2498_, v_a_2499_, lean_box(0));
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_dec_ref_known(v___x_2624_, 1);
goto v___jp_2549_;
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_inferType_2495_);
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2618_, 3);
goto v___jp_2549_;
}
}
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2636_; 
lean_del_object(v___x_2593_);
lean_dec(v_a_2545_);
lean_dec_ref(v_inferType_2495_);
v_val_2634_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2596_, 1);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_val_2634_);
v___x_2636_ = v___x_2547_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_val_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_inferType_2495_);
v_a_2644_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2544_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2544_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_dec_ref(v_e_2494_);
goto v___jp_2501_;
}
}
v___jp_2501_:
{
lean_object* v___x_2502_; lean_object* v_toApplicative_2503_; lean_object* v_toFunctor_2504_; lean_object* v_toSeq_2505_; lean_object* v_toSeqLeft_2506_; lean_object* v_toSeqRight_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_toCold_2523_; lean_object* v_cancelTk_x3f_2524_; 
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2503_ = lean_ctor_get(v___x_2502_, 0);
v_toFunctor_2504_ = lean_ctor_get(v_toApplicative_2503_, 0);
v_toSeq_2505_ = lean_ctor_get(v_toApplicative_2503_, 2);
v_toSeqLeft_2506_ = lean_ctor_get(v_toApplicative_2503_, 3);
v_toSeqRight_2507_ = lean_ctor_get(v_toApplicative_2503_, 4);
v___f_2508_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2509_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2504_, 2);
v___f_2510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2510_, 0, v_toFunctor_2504_);
v___f_2511_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2511_, 0, v_toFunctor_2504_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___f_2510_);
lean_ctor_set(v___x_2512_, 1, v___f_2511_);
lean_inc(v_toSeqRight_2507_);
v___f_2513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2513_, 0, v_toSeqRight_2507_);
lean_inc(v_toSeqLeft_2506_);
v___f_2514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2514_, 0, v_toSeqLeft_2506_);
lean_inc(v_toSeq_2505_);
v___f_2515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2515_, 0, v_toSeq_2505_);
v___x_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2512_);
lean_ctor_set(v___x_2516_, 1, v___f_2508_);
lean_ctor_set(v___x_2516_, 2, v___f_2515_);
lean_ctor_set(v___x_2516_, 3, v___f_2514_);
lean_ctor_set(v___x_2516_, 4, v___f_2513_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v___f_2509_);
v___x_2518_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2519_ = l_Lean_Core_instMonadRefCoreM;
v___x_2520_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2521_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2520_, v___x_2517_);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2518_);
lean_ctor_set(v___x_2522_, 1, v___x_2519_);
lean_ctor_set(v___x_2522_, 2, v___x_2521_);
v_toCold_2523_ = lean_ctor_get(v_a_2498_, 0);
v_cancelTk_x3f_2524_ = lean_ctor_get(v_toCold_2523_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2524_) == 1)
{
lean_object* v_val_2525_; uint8_t v___x_2526_; 
v_val_2525_ = lean_ctor_get(v_cancelTk_x3f_2524_, 0);
v___x_2526_ = l_IO_CancelToken_isSet(v_val_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec_ref_known(v___x_2522_, 3);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_a_2497_);
lean_inc_ref(v_a_2496_);
v___x_2527_ = lean_apply_5(v_inferType_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, lean_box(0));
return v___x_2527_;
}
else
{
lean_object* v___x_2047__overap_2528_; lean_object* v___x_2529_; 
v___x_2047__overap_2528_ = l_Lean_throwInterruptException___redArg(v___x_2522_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
v___x_2529_ = lean_apply_3(v___x_2047__overap_2528_, v_a_2498_, v_a_2499_, lean_box(0));
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref_known(v___x_2529_, 1);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_a_2497_);
lean_inc_ref(v_a_2496_);
v___x_2530_ = lean_apply_5(v_inferType_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, lean_box(0));
return v___x_2530_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_inferType_2495_);
v_a_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
else
{
lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2522_, 3);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_a_2497_);
lean_inc_ref(v_a_2496_);
v___x_2539_ = lean_apply_5(v_inferType_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, lean_box(0));
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2652_, lean_object* v_inferType_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2652_, v_inferType_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2712_; uint8_t v_beta_2713_; 
v___x_2712_ = l_Lean_Meta_Context_config(v___y_2661_);
v_beta_2713_ = lean_ctor_get_uint8(v___x_2712_, 13);
if (v_beta_2713_ == 0)
{
lean_dec_ref(v___x_2712_);
goto v___jp_2666_;
}
else
{
uint8_t v_iota_2714_; 
v_iota_2714_ = lean_ctor_get_uint8(v___x_2712_, 12);
if (v_iota_2714_ == 0)
{
lean_dec_ref(v___x_2712_);
goto v___jp_2666_;
}
else
{
uint8_t v_zeta_2715_; 
v_zeta_2715_ = lean_ctor_get_uint8(v___x_2712_, 15);
if (v_zeta_2715_ == 0)
{
lean_dec_ref(v___x_2712_);
goto v___jp_2666_;
}
else
{
uint8_t v_zetaHave_2716_; 
v_zetaHave_2716_ = lean_ctor_get_uint8(v___x_2712_, 18);
if (v_zetaHave_2716_ == 0)
{
lean_dec_ref(v___x_2712_);
goto v___jp_2666_;
}
else
{
uint8_t v_zetaDelta_2717_; 
v_zetaDelta_2717_ = lean_ctor_get_uint8(v___x_2712_, 16);
if (v_zetaDelta_2717_ == 0)
{
lean_dec_ref(v___x_2712_);
goto v___jp_2666_;
}
else
{
uint8_t v_etaStruct_2718_; uint8_t v_proj_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_etaStruct_2718_ = lean_ctor_get_uint8(v___x_2712_, 10);
v_proj_2719_ = lean_ctor_get_uint8(v___x_2712_, 14);
lean_dec_ref(v___x_2712_);
v___x_2720_ = lean_box(v_proj_2719_);
v___x_2721_ = lean_obj_tag_nat(v___x_2720_);
lean_dec(v___x_2720_);
v___x_2722_ = lean_unsigned_to_nat(2u);
v___x_2723_ = lean_nat_dec_eq(v___x_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
goto v___jp_2666_;
}
else
{
uint8_t v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = 0;
v___x_2725_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2718_, v___x_2724_);
if (v___x_2725_ == 0)
{
goto v___jp_2666_;
}
else
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_apply_5(v_x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, lean_box(0));
return v___x_2726_;
}
}
}
}
}
}
}
v___jp_2666_:
{
lean_object* v___x_2667_; uint8_t v_foApprox_2668_; uint8_t v_ctxApprox_2669_; uint8_t v_quasiPatternApprox_2670_; uint8_t v_constApprox_2671_; uint8_t v_isDefEqStuckEx_2672_; uint8_t v_unificationHints_2673_; uint8_t v_proofIrrelevance_2674_; uint8_t v_assignSyntheticOpaque_2675_; uint8_t v_offsetCnstrs_2676_; uint8_t v_transparency_2677_; uint8_t v_univApprox_2678_; uint8_t v_zetaUnused_2679_; uint8_t v_canUnfoldPredicateConfig_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2711_; 
v___x_2667_ = l_Lean_Meta_Context_config(v___y_2661_);
v_foApprox_2668_ = lean_ctor_get_uint8(v___x_2667_, 0);
v_ctxApprox_2669_ = lean_ctor_get_uint8(v___x_2667_, 1);
v_quasiPatternApprox_2670_ = lean_ctor_get_uint8(v___x_2667_, 2);
v_constApprox_2671_ = lean_ctor_get_uint8(v___x_2667_, 3);
v_isDefEqStuckEx_2672_ = lean_ctor_get_uint8(v___x_2667_, 4);
v_unificationHints_2673_ = lean_ctor_get_uint8(v___x_2667_, 5);
v_proofIrrelevance_2674_ = lean_ctor_get_uint8(v___x_2667_, 6);
v_assignSyntheticOpaque_2675_ = lean_ctor_get_uint8(v___x_2667_, 7);
v_offsetCnstrs_2676_ = lean_ctor_get_uint8(v___x_2667_, 8);
v_transparency_2677_ = lean_ctor_get_uint8(v___x_2667_, 9);
v_univApprox_2678_ = lean_ctor_get_uint8(v___x_2667_, 11);
v_zetaUnused_2679_ = lean_ctor_get_uint8(v___x_2667_, 17);
v_canUnfoldPredicateConfig_2680_ = lean_ctor_get_uint8(v___x_2667_, 19);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2682_ = v___x_2667_;
v_isShared_2683_ = v_isSharedCheck_2711_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v___x_2667_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2711_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint8_t v___x_2684_; uint8_t v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2688_; 
v___x_2684_ = 1;
v___x_2685_ = 0;
v___x_2686_ = 2;
if (v_isShared_2683_ == 0)
{
v___x_2688_ = v___x_2682_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 0, v_foApprox_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 1, v_ctxApprox_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 2, v_quasiPatternApprox_2670_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 3, v_constApprox_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 4, v_isDefEqStuckEx_2672_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 5, v_unificationHints_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 6, v_proofIrrelevance_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 7, v_assignSyntheticOpaque_2675_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 8, v_offsetCnstrs_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 9, v_transparency_2677_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 11, v_univApprox_2678_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 17, v_zetaUnused_2679_);
lean_ctor_set_uint8(v_reuseFailAlloc_2710_, 19, v_canUnfoldPredicateConfig_2680_);
v___x_2688_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
uint8_t v_trackZetaDelta_2689_; lean_object* v_zetaDeltaSet_2690_; lean_object* v_lctx_2691_; lean_object* v_localInstances_2692_; lean_object* v_defEqCtx_x3f_2693_; lean_object* v_synthPendingDepth_2694_; lean_object* v_customCanUnfoldPredicate_x3f_2695_; uint8_t v_univApprox_2696_; uint8_t v_inTypeClassResolution_2697_; uint8_t v_cacheInferType_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2708_; 
lean_ctor_set_uint8(v___x_2688_, 10, v___x_2685_);
lean_ctor_set_uint8(v___x_2688_, 12, v___x_2684_);
lean_ctor_set_uint8(v___x_2688_, 13, v___x_2684_);
lean_ctor_set_uint8(v___x_2688_, 14, v___x_2686_);
lean_ctor_set_uint8(v___x_2688_, 15, v___x_2684_);
lean_ctor_set_uint8(v___x_2688_, 16, v___x_2684_);
lean_ctor_set_uint8(v___x_2688_, 18, v___x_2684_);
v_trackZetaDelta_2689_ = lean_ctor_get_uint8(v___y_2661_, sizeof(void*)*7);
v_zetaDeltaSet_2690_ = lean_ctor_get(v___y_2661_, 1);
v_lctx_2691_ = lean_ctor_get(v___y_2661_, 2);
v_localInstances_2692_ = lean_ctor_get(v___y_2661_, 3);
v_defEqCtx_x3f_2693_ = lean_ctor_get(v___y_2661_, 4);
v_synthPendingDepth_2694_ = lean_ctor_get(v___y_2661_, 5);
v_customCanUnfoldPredicate_x3f_2695_ = lean_ctor_get(v___y_2661_, 6);
v_univApprox_2696_ = lean_ctor_get_uint8(v___y_2661_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2697_ = lean_ctor_get_uint8(v___y_2661_, sizeof(void*)*7 + 2);
v_cacheInferType_2698_ = lean_ctor_get_uint8(v___y_2661_, sizeof(void*)*7 + 3);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___y_2661_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___y_2661_, 0);
lean_dec(v_unused_2709_);
v___x_2700_ = v___y_2661_;
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2695_);
lean_inc(v_synthPendingDepth_2694_);
lean_inc(v_defEqCtx_x3f_2693_);
lean_inc(v_localInstances_2692_);
lean_inc(v_lctx_2691_);
lean_inc(v_zetaDeltaSet_2690_);
lean_dec(v___y_2661_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2708_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
uint64_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2688_);
v___x_2703_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2703_, 0, v___x_2688_);
lean_ctor_set_uint64(v___x_2703_, sizeof(void*)*1, v___x_2702_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2703_);
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_zetaDeltaSet_2690_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_lctx_2691_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_localInstances_2692_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_defEqCtx_x3f_2693_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_synthPendingDepth_2694_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_customCanUnfoldPredicate_x3f_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2707_, sizeof(void*)*7, v_trackZetaDelta_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2707_, sizeof(void*)*7 + 1, v_univApprox_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2707_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2707_, sizeof(void*)*7 + 3, v_cacheInferType_2698_);
v___x_2705_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_apply_5(v_x_2660_, v___x_2705_, v___y_2662_, v___y_2663_, v___y_2664_, lean_box(0));
return v___x_2706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v___y_2741_; lean_object* v___x_2758_; uint8_t v_transparency_2759_; uint8_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2758_ = l_Lean_Meta_Context_config(v_a_2735_);
v_transparency_2759_ = lean_ctor_get_uint8(v___x_2758_, 9);
lean_dec_ref(v___x_2758_);
v___x_2760_ = 1;
v___x_2761_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_inc(v_a_2738_);
lean_inc_ref(v_a_2737_);
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
v___x_2762_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
v___y_2741_ = v___x_2762_;
goto v___jp_2740_;
}
else
{
lean_object* v_keyedConfig_2763_; uint8_t v_trackZetaDelta_2764_; lean_object* v_zetaDeltaSet_2765_; lean_object* v_lctx_2766_; lean_object* v_localInstances_2767_; lean_object* v_defEqCtx_x3f_2768_; lean_object* v_synthPendingDepth_2769_; lean_object* v_customCanUnfoldPredicate_x3f_2770_; uint8_t v_univApprox_2771_; uint8_t v_inTypeClassResolution_2772_; uint8_t v_cacheInferType_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_keyedConfig_2763_ = lean_ctor_get(v_a_2735_, 0);
v_trackZetaDelta_2764_ = lean_ctor_get_uint8(v_a_2735_, sizeof(void*)*7);
v_zetaDeltaSet_2765_ = lean_ctor_get(v_a_2735_, 1);
v_lctx_2766_ = lean_ctor_get(v_a_2735_, 2);
v_localInstances_2767_ = lean_ctor_get(v_a_2735_, 3);
v_defEqCtx_x3f_2768_ = lean_ctor_get(v_a_2735_, 4);
v_synthPendingDepth_2769_ = lean_ctor_get(v_a_2735_, 5);
v_customCanUnfoldPredicate_x3f_2770_ = lean_ctor_get(v_a_2735_, 6);
v_univApprox_2771_ = lean_ctor_get_uint8(v_a_2735_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2772_ = lean_ctor_get_uint8(v_a_2735_, sizeof(void*)*7 + 2);
v_cacheInferType_2773_ = lean_ctor_get_uint8(v_a_2735_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2763_);
v___x_2774_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2760_, v_keyedConfig_2763_);
lean_inc(v_customCanUnfoldPredicate_x3f_2770_);
lean_inc(v_synthPendingDepth_2769_);
lean_inc(v_defEqCtx_x3f_2768_);
lean_inc_ref(v_localInstances_2767_);
lean_inc_ref(v_lctx_2766_);
lean_inc(v_zetaDeltaSet_2765_);
v___x_2775_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_zetaDeltaSet_2765_);
lean_ctor_set(v___x_2775_, 2, v_lctx_2766_);
lean_ctor_set(v___x_2775_, 3, v_localInstances_2767_);
lean_ctor_set(v___x_2775_, 4, v_defEqCtx_x3f_2768_);
lean_ctor_set(v___x_2775_, 5, v_synthPendingDepth_2769_);
lean_ctor_set(v___x_2775_, 6, v_customCanUnfoldPredicate_x3f_2770_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*7, v_trackZetaDelta_2764_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*7 + 1, v_univApprox_2771_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2772_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*7 + 3, v_cacheInferType_2773_);
lean_inc(v_a_2738_);
lean_inc_ref(v_a_2737_);
lean_inc(v_a_2736_);
v___x_2776_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2734_, v___x_2775_, v_a_2736_, v_a_2737_, v_a_2738_);
v___y_2741_ = v___x_2776_;
goto v___jp_2740_;
}
v___jp_2740_:
{
if (lean_obj_tag(v___y_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_a_2742_ = lean_ctor_get(v___y_2741_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___y_2741_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___y_2741_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___y_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
v_a_2750_ = lean_ctor_get(v___y_2741_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___y_2741_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___y_2741_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___y_2741_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2784_, lean_object* v_x_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___y_2792_; lean_object* v___x_2809_; uint8_t v_transparency_2810_; uint8_t v___x_2811_; uint8_t v___x_2812_; 
v___x_2809_ = l_Lean_Meta_Context_config(v_a_2786_);
v_transparency_2810_ = lean_ctor_get_uint8(v___x_2809_, 9);
lean_dec_ref(v___x_2809_);
v___x_2811_ = 1;
v___x_2812_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
v___x_2813_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
v___y_2792_ = v___x_2813_;
goto v___jp_2791_;
}
else
{
lean_object* v_keyedConfig_2814_; uint8_t v_trackZetaDelta_2815_; lean_object* v_zetaDeltaSet_2816_; lean_object* v_lctx_2817_; lean_object* v_localInstances_2818_; lean_object* v_defEqCtx_x3f_2819_; lean_object* v_synthPendingDepth_2820_; lean_object* v_customCanUnfoldPredicate_x3f_2821_; uint8_t v_univApprox_2822_; uint8_t v_inTypeClassResolution_2823_; uint8_t v_cacheInferType_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_keyedConfig_2814_ = lean_ctor_get(v_a_2786_, 0);
v_trackZetaDelta_2815_ = lean_ctor_get_uint8(v_a_2786_, sizeof(void*)*7);
v_zetaDeltaSet_2816_ = lean_ctor_get(v_a_2786_, 1);
v_lctx_2817_ = lean_ctor_get(v_a_2786_, 2);
v_localInstances_2818_ = lean_ctor_get(v_a_2786_, 3);
v_defEqCtx_x3f_2819_ = lean_ctor_get(v_a_2786_, 4);
v_synthPendingDepth_2820_ = lean_ctor_get(v_a_2786_, 5);
v_customCanUnfoldPredicate_x3f_2821_ = lean_ctor_get(v_a_2786_, 6);
v_univApprox_2822_ = lean_ctor_get_uint8(v_a_2786_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2823_ = lean_ctor_get_uint8(v_a_2786_, sizeof(void*)*7 + 2);
v_cacheInferType_2824_ = lean_ctor_get_uint8(v_a_2786_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2814_);
v___x_2825_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2811_, v_keyedConfig_2814_);
lean_inc(v_customCanUnfoldPredicate_x3f_2821_);
lean_inc(v_synthPendingDepth_2820_);
lean_inc(v_defEqCtx_x3f_2819_);
lean_inc_ref(v_localInstances_2818_);
lean_inc_ref(v_lctx_2817_);
lean_inc(v_zetaDeltaSet_2816_);
v___x_2826_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v_zetaDeltaSet_2816_);
lean_ctor_set(v___x_2826_, 2, v_lctx_2817_);
lean_ctor_set(v___x_2826_, 3, v_localInstances_2818_);
lean_ctor_set(v___x_2826_, 4, v_defEqCtx_x3f_2819_);
lean_ctor_set(v___x_2826_, 5, v_synthPendingDepth_2820_);
lean_ctor_set(v___x_2826_, 6, v_customCanUnfoldPredicate_x3f_2821_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*7, v_trackZetaDelta_2815_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*7 + 1, v_univApprox_2822_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2823_);
lean_ctor_set_uint8(v___x_2826_, sizeof(void*)*7 + 3, v_cacheInferType_2824_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
v___x_2827_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2785_, v___x_2826_, v_a_2787_, v_a_2788_, v_a_2789_);
v___y_2792_ = v___x_2827_;
goto v___jp_2791_;
}
v___jp_2791_:
{
if (lean_obj_tag(v___y_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___y_2792_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___y_2792_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___y_2792_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___y_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___y_2792_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___y_2792_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___y_2792_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___y_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_x_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2828_, v_x_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2835_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = l_Lean_interruptExceptionId;
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2854_, lean_object* v_x_2855_, lean_object* v_x_2856_, lean_object* v_x_2857_){
_start:
{
lean_object* v_ks_2858_; lean_object* v_vs_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2885_; 
v_ks_2858_ = lean_ctor_get(v_x_2854_, 0);
v_vs_2859_ = lean_ctor_get(v_x_2854_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_x_2854_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2861_ = v_x_2854_;
v_isShared_2862_ = v_isSharedCheck_2885_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_vs_2859_);
lean_inc(v_ks_2858_);
lean_dec(v_x_2854_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2885_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_array_get_size(v_ks_2858_);
v___x_2871_ = lean_nat_dec_lt(v_x_2855_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_del_object(v___x_2861_);
lean_dec(v_x_2855_);
v___x_2872_ = lean_array_push(v_ks_2858_, v_x_2856_);
v___x_2873_ = lean_array_push(v_vs_2859_, v_x_2857_);
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
return v___x_2874_;
}
else
{
lean_object* v_expr_2875_; uint64_t v_configKey_2876_; lean_object* v_k_x27_2877_; lean_object* v_expr_2878_; uint64_t v_configKey_2879_; uint8_t v___x_2880_; 
v_expr_2875_ = lean_ctor_get(v_x_2856_, 0);
v_configKey_2876_ = lean_ctor_get_uint64(v_x_2856_, sizeof(void*)*1);
v_k_x27_2877_ = lean_array_fget_borrowed(v_ks_2858_, v_x_2855_);
v_expr_2878_ = lean_ctor_get(v_k_x27_2877_, 0);
v_configKey_2879_ = lean_ctor_get_uint64(v_k_x27_2877_, sizeof(void*)*1);
v___x_2880_ = lean_expr_equal(v_expr_2875_, v_expr_2878_);
if (v___x_2880_ == 0)
{
goto v___jp_2863_;
}
else
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_uint64_dec_eq(v_configKey_2876_, v_configKey_2879_);
if (v___x_2881_ == 0)
{
goto v___jp_2863_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_del_object(v___x_2861_);
v___x_2882_ = lean_array_fset(v_ks_2858_, v_x_2855_, v_x_2856_);
v___x_2883_ = lean_array_fset(v_vs_2859_, v_x_2855_, v_x_2857_);
lean_dec(v_x_2855_);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
return v___x_2884_;
}
}
}
v___jp_2863_:
{
lean_object* v___x_2865_; 
if (v_isShared_2862_ == 0)
{
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_ks_2858_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_vs_2859_);
v___x_2865_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_unsigned_to_nat(1u);
v___x_2867_ = lean_nat_add(v_x_2855_, v___x_2866_);
lean_dec(v_x_2855_);
v_x_2854_ = v___x_2865_;
v_x_2855_ = v___x_2867_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2886_, lean_object* v_k_2887_, lean_object* v_v_2888_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2886_, v___x_2889_, v_k_2887_, v_v_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2891_, size_t v_x_2892_, size_t v_x_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
if (lean_obj_tag(v_x_2891_) == 0)
{
lean_object* v_es_2896_; size_t v___x_2897_; size_t v___x_2898_; lean_object* v_j_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v_es_2896_ = lean_ctor_get(v_x_2891_, 0);
v___x_2897_ = ((size_t)31ULL);
v___x_2898_ = lean_usize_land(v_x_2892_, v___x_2897_);
v_j_2899_ = lean_usize_to_nat(v___x_2898_);
v___x_2900_ = lean_array_get_size(v_es_2896_);
v___x_2901_ = lean_nat_dec_lt(v_j_2899_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_dec(v_j_2899_);
lean_dec(v_x_2895_);
lean_dec_ref(v_x_2894_);
return v_x_2891_;
}
else
{
lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2946_; 
lean_inc_ref(v_es_2896_);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_x_2891_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v_x_2891_, 0);
lean_dec(v_unused_2947_);
v___x_2903_ = v_x_2891_;
v_isShared_2904_ = v_isSharedCheck_2946_;
goto v_resetjp_2902_;
}
else
{
lean_dec(v_x_2891_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2946_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_v_2905_; lean_object* v___x_2906_; lean_object* v_xs_x27_2907_; lean_object* v___y_2909_; 
v_v_2905_ = lean_array_fget(v_es_2896_, v_j_2899_);
v___x_2906_ = lean_box(0);
v_xs_x27_2907_ = lean_array_fset(v_es_2896_, v_j_2899_, v___x_2906_);
switch(lean_obj_tag(v_v_2905_))
{
case 0:
{
lean_object* v_key_2914_; lean_object* v_val_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2931_; 
v_key_2914_ = lean_ctor_get(v_v_2905_, 0);
v_val_2915_ = lean_ctor_get(v_v_2905_, 1);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_v_2905_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2917_ = v_v_2905_;
v_isShared_2918_ = v_isSharedCheck_2931_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_val_2915_);
lean_inc(v_key_2914_);
lean_dec(v_v_2905_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2931_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_expr_2922_; uint64_t v_configKey_2923_; lean_object* v_expr_2924_; uint64_t v_configKey_2925_; uint8_t v___x_2926_; 
v_expr_2922_ = lean_ctor_get(v_x_2894_, 0);
v_configKey_2923_ = lean_ctor_get_uint64(v_x_2894_, sizeof(void*)*1);
v_expr_2924_ = lean_ctor_get(v_key_2914_, 0);
v_configKey_2925_ = lean_ctor_get_uint64(v_key_2914_, sizeof(void*)*1);
v___x_2926_ = lean_expr_equal(v_expr_2922_, v_expr_2924_);
if (v___x_2926_ == 0)
{
lean_del_object(v___x_2917_);
goto v___jp_2919_;
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_uint64_dec_eq(v_configKey_2923_, v_configKey_2925_);
if (v___x_2927_ == 0)
{
lean_del_object(v___x_2917_);
goto v___jp_2919_;
}
else
{
lean_object* v___x_2929_; 
lean_dec(v_val_2915_);
lean_dec(v_key_2914_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v_x_2895_);
lean_ctor_set(v___x_2917_, 0, v_x_2894_);
v___x_2929_ = v___x_2917_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_x_2894_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_x_2895_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
v___y_2909_ = v___x_2929_;
goto v___jp_2908_;
}
}
}
v___jp_2919_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2914_, v_val_2915_, v_x_2894_, v_x_2895_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___y_2909_ = v___x_2921_;
goto v___jp_2908_;
}
}
}
case 1:
{
lean_object* v_node_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2944_; 
v_node_2932_ = lean_ctor_get(v_v_2905_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_v_2905_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2934_ = v_v_2905_;
v_isShared_2935_ = v_isSharedCheck_2944_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_node_2932_);
lean_dec(v_v_2905_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2944_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
size_t v___x_2936_; size_t v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2936_ = ((size_t)5ULL);
v___x_2937_ = lean_usize_shift_right(v_x_2892_, v___x_2936_);
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_x_2893_, v___x_2938_);
v___x_2940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2932_, v___x_2937_, v___x_2939_, v_x_2894_, v_x_2895_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2940_);
v___x_2942_ = v___x_2934_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v___y_2909_ = v___x_2942_;
goto v___jp_2908_;
}
}
}
default: 
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_x_2894_);
lean_ctor_set(v___x_2945_, 1, v_x_2895_);
v___y_2909_ = v___x_2945_;
goto v___jp_2908_;
}
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = lean_array_fset(v_xs_x27_2907_, v_j_2899_, v___y_2909_);
lean_dec(v_j_2899_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2910_);
v___x_2912_ = v___x_2903_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
else
{
lean_object* v_ks_2948_; lean_object* v_vs_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2967_; 
v_ks_2948_ = lean_ctor_get(v_x_2891_, 0);
v_vs_2949_ = lean_ctor_get(v_x_2891_, 1);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_x_2891_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2951_ = v_x_2891_;
v_isShared_2952_ = v_isSharedCheck_2967_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_vs_2949_);
lean_inc(v_ks_2948_);
lean_dec(v_x_2891_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2967_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_ks_2948_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_vs_2949_);
v___x_2954_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v_newNode_2955_; size_t v___x_2956_; uint8_t v___x_2957_; 
v_newNode_2955_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2954_, v_x_2894_, v_x_2895_);
v___x_2956_ = ((size_t)7ULL);
v___x_2957_ = lean_usize_dec_le(v___x_2956_, v_x_2893_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2958_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2955_);
v___x_2959_ = lean_unsigned_to_nat(4u);
v___x_2960_ = lean_nat_dec_lt(v___x_2958_, v___x_2959_);
lean_dec(v___x_2958_);
if (v___x_2960_ == 0)
{
lean_object* v_ks_2961_; lean_object* v_vs_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_ks_2961_ = lean_ctor_get(v_newNode_2955_, 0);
lean_inc_ref(v_ks_2961_);
v_vs_2962_ = lean_ctor_get(v_newNode_2955_, 1);
lean_inc_ref(v_vs_2962_);
lean_dec_ref(v_newNode_2955_);
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2893_, v_ks_2961_, v_vs_2962_, v___x_2963_, v___x_2964_);
lean_dec_ref(v_vs_2962_);
lean_dec_ref(v_ks_2961_);
return v___x_2965_;
}
else
{
return v_newNode_2955_;
}
}
else
{
return v_newNode_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2968_, lean_object* v_keys_2969_, lean_object* v_vals_2970_, lean_object* v_i_2971_, lean_object* v_entries_2972_){
_start:
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = lean_array_get_size(v_keys_2969_);
v___x_2974_ = lean_nat_dec_lt(v_i_2971_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v_i_2971_);
return v_entries_2972_;
}
else
{
lean_object* v_k_2975_; lean_object* v_expr_2976_; uint64_t v_configKey_2977_; lean_object* v_v_2978_; uint64_t v___x_2979_; uint64_t v___x_2980_; size_t v_h_2981_; size_t v___x_2982_; lean_object* v___x_2983_; size_t v___x_2984_; size_t v___x_2985_; size_t v___x_2986_; size_t v_h_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_k_2975_ = lean_array_fget_borrowed(v_keys_2969_, v_i_2971_);
v_expr_2976_ = lean_ctor_get(v_k_2975_, 0);
v_configKey_2977_ = lean_ctor_get_uint64(v_k_2975_, sizeof(void*)*1);
v_v_2978_ = lean_array_fget_borrowed(v_vals_2970_, v_i_2971_);
v___x_2979_ = l_Lean_Expr_hash(v_expr_2976_);
v___x_2980_ = lean_uint64_mix_hash(v___x_2979_, v_configKey_2977_);
v_h_2981_ = lean_uint64_to_usize(v___x_2980_);
v___x_2982_ = ((size_t)5ULL);
v___x_2983_ = lean_unsigned_to_nat(1u);
v___x_2984_ = ((size_t)1ULL);
v___x_2985_ = lean_usize_sub(v_depth_2968_, v___x_2984_);
v___x_2986_ = lean_usize_mul(v___x_2982_, v___x_2985_);
v_h_2987_ = lean_usize_shift_right(v_h_2981_, v___x_2986_);
v___x_2988_ = lean_nat_add(v_i_2971_, v___x_2983_);
lean_dec(v_i_2971_);
lean_inc(v_v_2978_);
lean_inc(v_k_2975_);
v___x_2989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2972_, v_h_2987_, v_depth_2968_, v_k_2975_, v_v_2978_);
v_i_2971_ = v___x_2988_;
v_entries_2972_ = v___x_2989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2991_, lean_object* v_keys_2992_, lean_object* v_vals_2993_, lean_object* v_i_2994_, lean_object* v_entries_2995_){
_start:
{
size_t v_depth_boxed_2996_; lean_object* v_res_2997_; 
v_depth_boxed_2996_ = lean_unbox_usize(v_depth_2991_);
lean_dec(v_depth_2991_);
v_res_2997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2996_, v_keys_2992_, v_vals_2993_, v_i_2994_, v_entries_2995_);
lean_dec_ref(v_vals_2993_);
lean_dec_ref(v_keys_2992_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
size_t v_x_2430__boxed_3003_; size_t v_x_2431__boxed_3004_; lean_object* v_res_3005_; 
v_x_2430__boxed_3003_ = lean_unbox_usize(v_x_2999_);
lean_dec(v_x_2999_);
v_x_2431__boxed_3004_ = lean_unbox_usize(v_x_3000_);
lean_dec(v_x_3000_);
v_res_3005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2998_, v_x_2430__boxed_3003_, v_x_2431__boxed_3004_, v_x_3001_, v_x_3002_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v_expr_3009_; uint64_t v_configKey_3010_; uint64_t v___x_3011_; uint64_t v___x_3012_; size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v_expr_3009_ = lean_ctor_get(v_x_3007_, 0);
v_configKey_3010_ = lean_ctor_get_uint64(v_x_3007_, sizeof(void*)*1);
v___x_3011_ = l_Lean_Expr_hash(v_expr_3009_);
v___x_3012_ = lean_uint64_mix_hash(v___x_3011_, v_configKey_3010_);
v___x_3013_ = lean_uint64_to_usize(v___x_3012_);
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3006_, v___x_3013_, v___x_3014_, v_x_3007_, v_x_3008_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3016_, lean_object* v_vals_3017_, lean_object* v_i_3018_, lean_object* v_k_3019_){
_start:
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = lean_array_get_size(v_keys_3016_);
v___x_3025_ = lean_nat_dec_lt(v_i_3018_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v_i_3018_);
v___x_3026_ = lean_box(0);
return v___x_3026_;
}
else
{
lean_object* v_expr_3027_; uint64_t v_configKey_3028_; lean_object* v_k_x27_3029_; lean_object* v_expr_3030_; uint64_t v_configKey_3031_; uint8_t v___x_3032_; 
v_expr_3027_ = lean_ctor_get(v_k_3019_, 0);
v_configKey_3028_ = lean_ctor_get_uint64(v_k_3019_, sizeof(void*)*1);
v_k_x27_3029_ = lean_array_fget_borrowed(v_keys_3016_, v_i_3018_);
v_expr_3030_ = lean_ctor_get(v_k_x27_3029_, 0);
v_configKey_3031_ = lean_ctor_get_uint64(v_k_x27_3029_, sizeof(void*)*1);
v___x_3032_ = lean_expr_equal(v_expr_3027_, v_expr_3030_);
if (v___x_3032_ == 0)
{
goto v___jp_3020_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_uint64_dec_eq(v_configKey_3028_, v_configKey_3031_);
if (v___x_3033_ == 0)
{
goto v___jp_3020_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_array_fget_borrowed(v_vals_3017_, v_i_3018_);
lean_dec(v_i_3018_);
lean_inc(v___x_3034_);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
}
v___jp_3020_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_unsigned_to_nat(1u);
v___x_3022_ = lean_nat_add(v_i_3018_, v___x_3021_);
lean_dec(v_i_3018_);
v_i_3018_ = v___x_3022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3036_, lean_object* v_vals_3037_, lean_object* v_i_3038_, lean_object* v_k_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3036_, v_vals_3037_, v_i_3038_, v_k_3039_);
lean_dec_ref(v_k_3039_);
lean_dec_ref(v_vals_3037_);
lean_dec_ref(v_keys_3036_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3041_, size_t v_x_3042_, lean_object* v_x_3043_){
_start:
{
if (lean_obj_tag(v_x_3041_) == 0)
{
lean_object* v_es_3044_; lean_object* v___x_3045_; size_t v___x_3046_; size_t v___x_3047_; lean_object* v_j_3048_; lean_object* v___x_3049_; 
v_es_3044_ = lean_ctor_get(v_x_3041_, 0);
v___x_3045_ = lean_box(2);
v___x_3046_ = ((size_t)31ULL);
v___x_3047_ = lean_usize_land(v_x_3042_, v___x_3046_);
v_j_3048_ = lean_usize_to_nat(v___x_3047_);
v___x_3049_ = lean_array_get_borrowed(v___x_3045_, v_es_3044_, v_j_3048_);
lean_dec(v_j_3048_);
switch(lean_obj_tag(v___x_3049_))
{
case 0:
{
lean_object* v_key_3050_; lean_object* v_val_3051_; lean_object* v_expr_3052_; uint64_t v_configKey_3053_; lean_object* v_expr_3054_; uint64_t v_configKey_3055_; uint8_t v___x_3056_; 
v_key_3050_ = lean_ctor_get(v___x_3049_, 0);
v_val_3051_ = lean_ctor_get(v___x_3049_, 1);
v_expr_3052_ = lean_ctor_get(v_x_3043_, 0);
v_configKey_3053_ = lean_ctor_get_uint64(v_x_3043_, sizeof(void*)*1);
v_expr_3054_ = lean_ctor_get(v_key_3050_, 0);
v_configKey_3055_ = lean_ctor_get_uint64(v_key_3050_, sizeof(void*)*1);
v___x_3056_ = lean_expr_equal(v_expr_3052_, v_expr_3054_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_box(0);
return v___x_3057_;
}
else
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_uint64_dec_eq(v_configKey_3053_, v_configKey_3055_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; 
lean_inc(v_val_3051_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_val_3051_);
return v___x_3060_;
}
}
}
case 1:
{
lean_object* v_node_3061_; size_t v___x_3062_; size_t v___x_3063_; 
v_node_3061_ = lean_ctor_get(v___x_3049_, 0);
v___x_3062_ = ((size_t)5ULL);
v___x_3063_ = lean_usize_shift_right(v_x_3042_, v___x_3062_);
v_x_3041_ = v_node_3061_;
v_x_3042_ = v___x_3063_;
goto _start;
}
default: 
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_box(0);
return v___x_3065_;
}
}
}
else
{
lean_object* v_ks_3066_; lean_object* v_vs_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_ks_3066_ = lean_ctor_get(v_x_3041_, 0);
v_vs_3067_ = lean_ctor_get(v_x_3041_, 1);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3066_, v_vs_3067_, v___x_3068_, v_x_3043_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_){
_start:
{
size_t v_x_2630__boxed_3073_; lean_object* v_res_3074_; 
v_x_2630__boxed_3073_ = lean_unbox_usize(v_x_3071_);
lean_dec(v_x_3071_);
v_res_3074_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3070_, v_x_2630__boxed_3073_, v_x_3072_);
lean_dec_ref(v_x_3072_);
lean_dec_ref(v_x_3070_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
lean_object* v_expr_3077_; uint64_t v_configKey_3078_; uint64_t v___x_3079_; uint64_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v_expr_3077_ = lean_ctor_get(v_x_3076_, 0);
v_configKey_3078_ = lean_ctor_get_uint64(v_x_3076_, sizeof(void*)*1);
v___x_3079_ = l_Lean_Expr_hash(v_expr_3077_);
v___x_3080_ = lean_uint64_mix_hash(v___x_3079_, v_configKey_3078_);
v___x_3081_ = lean_uint64_to_usize(v___x_3080_);
v___x_3082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3075_, v___x_3081_, v_x_3076_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3083_, v_x_3084_);
lean_dec_ref(v_x_3084_);
lean_dec_ref(v_x_3083_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3088_ = l_Lean_stringToMessageData(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
switch(lean_obj_tag(v_e_3089_))
{
case 0:
{
lean_object* v_deBruijnIndex_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_deBruijnIndex_3127_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_deBruijnIndex_3127_);
lean_dec_ref_known(v_e_3089_, 1);
v___x_3128_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3129_ = l_Lean_mkBVar(v_deBruijnIndex_3127_);
v___x_3130_ = l_Lean_MessageData_ofExpr(v___x_3129_);
v___x_3131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3128_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3131_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3132_;
}
case 1:
{
lean_object* v_fvarId_3133_; lean_object* v___x_3134_; 
v_fvarId_3133_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_fvarId_3133_);
lean_dec_ref_known(v_e_3089_, 1);
v___x_3134_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3133_, v_a_3090_, v_a_3092_, v_a_3093_);
return v___x_3134_;
}
case 2:
{
lean_object* v_mvarId_3135_; lean_object* v___x_3136_; 
v_mvarId_3135_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_mvarId_3135_);
lean_dec_ref_known(v_e_3089_, 1);
v___x_3136_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3135_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3136_;
}
case 3:
{
lean_object* v_u_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_u_3137_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_u_3137_);
lean_dec_ref_known(v_e_3089_, 1);
v___x_3138_ = l_Lean_Level_succ___override(v_u_3137_);
v___x_3139_ = l_Lean_mkSort(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
case 4:
{
lean_object* v_declName_3141_; lean_object* v_us_3142_; 
v_declName_3141_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_declName_3141_);
v_us_3142_ = lean_ctor_get(v_e_3089_, 1);
lean_inc(v_us_3142_);
if (lean_obj_tag(v_us_3142_) == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref_known(v_e_3089_, 2);
v___x_3159_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3141_, v_us_3142_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3159_;
}
else
{
uint8_t v_cacheInferType_3160_; 
v_cacheInferType_3160_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3160_ == 0)
{
lean_dec_ref_known(v_e_3089_, 2);
goto v___jp_3143_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = l_Lean_Expr_hasMVar(v_e_3089_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3229_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3229_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3229_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3208_; lean_object* v_cache_3209_; lean_object* v_inferType_3210_; lean_object* v___x_3211_; 
v___x_3208_ = lean_st_ref_get(v_a_3091_);
v_cache_3209_ = lean_ctor_get(v___x_3208_, 1);
lean_inc_ref(v_cache_3209_);
lean_dec(v___x_3208_);
v_inferType_3210_ = lean_ctor_get(v_cache_3209_, 0);
lean_inc_ref(v_inferType_3210_);
lean_dec_ref(v_cache_3209_);
v___x_3211_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3210_, v_a_3163_);
lean_dec_ref(v_inferType_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_toCold_3212_; lean_object* v_cancelTk_x3f_3213_; 
lean_del_object(v___x_3165_);
v_toCold_3212_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3213_ = lean_ctor_get(v_toCold_3212_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3213_) == 1)
{
lean_object* v_val_3214_; uint8_t v___x_3215_; 
v_val_3214_ = lean_ctor_get(v_cancelTk_x3f_3213_, 0);
v___x_3215_ = l_IO_CancelToken_isSet(v_val_3214_);
if (v___x_3215_ == 0)
{
goto v___jp_3167_;
}
else
{
lean_object* v___x_3216_; lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3163_);
lean_dec(v_us_3142_);
lean_dec(v_declName_3141_);
v___x_3216_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
goto v___jp_3167_;
}
}
else
{
lean_object* v_val_3225_; lean_object* v___x_3227_; 
lean_dec(v_a_3163_);
lean_dec(v_us_3142_);
lean_dec(v_declName_3141_);
v_val_3225_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_val_3225_);
lean_dec_ref_known(v___x_3211_, 1);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v_val_3225_);
v___x_3227_ = v___x_3165_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_val_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
v___jp_3167_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3141_, v_us_3142_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; uint8_t v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v___x_3170_ = l_Lean_Expr_hasMVar(v_a_3169_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3206_; 
lean_inc(v_a_3169_);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3168_, 0);
lean_dec(v_unused_3207_);
v___x_3172_ = v___x_3168_;
v_isShared_3173_ = v_isSharedCheck_3206_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v___x_3168_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3206_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v_cache_3175_; lean_object* v_mctx_3176_; lean_object* v_zetaDeltaFVarIds_3177_; lean_object* v_postponed_3178_; lean_object* v_diag_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3205_; 
v___x_3174_ = lean_st_ref_take(v_a_3091_);
v_cache_3175_ = lean_ctor_get(v___x_3174_, 1);
v_mctx_3176_ = lean_ctor_get(v___x_3174_, 0);
v_zetaDeltaFVarIds_3177_ = lean_ctor_get(v___x_3174_, 2);
v_postponed_3178_ = lean_ctor_get(v___x_3174_, 3);
v_diag_3179_ = lean_ctor_get(v___x_3174_, 4);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3181_ = v___x_3174_;
v_isShared_3182_ = v_isSharedCheck_3205_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_diag_3179_);
lean_inc(v_postponed_3178_);
lean_inc(v_zetaDeltaFVarIds_3177_);
lean_inc(v_cache_3175_);
lean_inc(v_mctx_3176_);
lean_dec(v___x_3174_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3205_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_inferType_3183_; lean_object* v_funInfo_3184_; lean_object* v_synthInstance_3185_; lean_object* v_whnf_3186_; lean_object* v_defEqTrans_3187_; lean_object* v_defEqPerm_3188_; lean_object* v_isUnitLike_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3204_; 
v_inferType_3183_ = lean_ctor_get(v_cache_3175_, 0);
v_funInfo_3184_ = lean_ctor_get(v_cache_3175_, 1);
v_synthInstance_3185_ = lean_ctor_get(v_cache_3175_, 2);
v_whnf_3186_ = lean_ctor_get(v_cache_3175_, 3);
v_defEqTrans_3187_ = lean_ctor_get(v_cache_3175_, 4);
v_defEqPerm_3188_ = lean_ctor_get(v_cache_3175_, 5);
v_isUnitLike_3189_ = lean_ctor_get(v_cache_3175_, 6);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_cache_3175_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3191_ = v_cache_3175_;
v_isShared_3192_ = v_isSharedCheck_3204_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_isUnitLike_3189_);
lean_inc(v_defEqPerm_3188_);
lean_inc(v_defEqTrans_3187_);
lean_inc(v_whnf_3186_);
lean_inc(v_synthInstance_3185_);
lean_inc(v_funInfo_3184_);
lean_inc(v_inferType_3183_);
lean_dec(v_cache_3175_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3204_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_inc(v_a_3169_);
v___x_3193_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3183_, v_a_3163_, v_a_3169_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_funInfo_3184_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_synthInstance_3185_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_whnf_3186_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_defEqTrans_3187_);
lean_ctor_set(v_reuseFailAlloc_3203_, 5, v_defEqPerm_3188_);
lean_ctor_set(v_reuseFailAlloc_3203_, 6, v_isUnitLike_3189_);
v___x_3195_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3197_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3195_);
v___x_3197_ = v___x_3181_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_mctx_3176_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_zetaDeltaFVarIds_3177_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_postponed_3178_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_diag_3179_);
v___x_3197_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_st_ref_put(v_a_3091_, v___x_3197_);
if (v_isShared_3173_ == 0)
{
v___x_3200_ = v___x_3172_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3169_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3163_);
return v___x_3168_;
}
}
else
{
lean_dec(v_a_3163_);
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_us_3142_);
lean_dec(v_declName_3141_);
v_a_3230_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3162_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3162_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3089_, 2);
goto v___jp_3143_;
}
}
}
v___jp_3143_:
{
lean_object* v_toCold_3144_; lean_object* v_cancelTk_x3f_3145_; 
v_toCold_3144_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3145_ = lean_ctor_get(v_toCold_3144_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3145_) == 1)
{
lean_object* v_val_3146_; uint8_t v___x_3147_; 
v_val_3146_ = lean_ctor_get(v_cancelTk_x3f_3145_, 0);
v___x_3147_ = l_IO_CancelToken_isSet(v_val_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3141_, v_us_3142_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_us_3142_);
lean_dec(v_declName_3141_);
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
v___x_3158_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3141_, v_us_3142_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3158_;
}
}
}
case 5:
{
lean_object* v_fn_3238_; uint8_t v_cacheInferType_3239_; lean_object* v_nargs_3240_; lean_object* v___x_3241_; lean_object* v_dummy_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_fn_3238_ = lean_ctor_get(v_e_3089_, 0);
v_cacheInferType_3239_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*7 + 3);
v_nargs_3240_ = l_Lean_Expr_getAppNumArgs(v_e_3089_);
v___x_3241_ = l_Lean_Expr_getAppFn(v_fn_3238_);
v_dummy_3242_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3240_);
v___x_3243_ = lean_mk_array(v_nargs_3240_, v_dummy_3242_);
v___x_3244_ = lean_unsigned_to_nat(1u);
v___x_3245_ = lean_nat_sub(v_nargs_3240_, v___x_3244_);
lean_dec(v_nargs_3240_);
lean_inc_ref(v_e_3089_);
v___x_3246_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3089_, v___x_3243_, v___x_3245_);
if (v_cacheInferType_3239_ == 0)
{
lean_dec_ref_known(v_e_3089_, 2);
goto v___jp_3247_;
}
else
{
uint8_t v___x_3263_; 
v___x_3263_ = l_Lean_Expr_hasMVar(v_e_3089_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3331_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3267_ = v___x_3264_;
v_isShared_3268_ = v_isSharedCheck_3331_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3331_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3310_; lean_object* v_cache_3311_; lean_object* v_inferType_3312_; lean_object* v___x_3313_; 
v___x_3310_ = lean_st_ref_get(v_a_3091_);
v_cache_3311_ = lean_ctor_get(v___x_3310_, 1);
lean_inc_ref(v_cache_3311_);
lean_dec(v___x_3310_);
v_inferType_3312_ = lean_ctor_get(v_cache_3311_, 0);
lean_inc_ref(v_inferType_3312_);
lean_dec_ref(v_cache_3311_);
v___x_3313_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3312_, v_a_3265_);
lean_dec_ref(v_inferType_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_toCold_3314_; lean_object* v_cancelTk_x3f_3315_; 
lean_del_object(v___x_3267_);
v_toCold_3314_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3315_ = lean_ctor_get(v_toCold_3314_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3315_) == 1)
{
lean_object* v_val_3316_; uint8_t v___x_3317_; 
v_val_3316_ = lean_ctor_get(v_cancelTk_x3f_3315_, 0);
v___x_3317_ = l_IO_CancelToken_isSet(v_val_3316_);
if (v___x_3317_ == 0)
{
goto v___jp_3269_;
}
else
{
lean_object* v___x_3318_; lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3241_);
v___x_3318_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
goto v___jp_3269_;
}
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3329_; 
lean_dec(v_a_3265_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3241_);
v_val_3327_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v___x_3313_, 1);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v_val_3327_);
v___x_3329_ = v___x_3267_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_val_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
v___jp_3269_:
{
lean_object* v___x_3270_; 
v___x_3270_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3241_, v___x_3246_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec_ref(v___x_3246_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; uint8_t v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v___x_3272_ = l_Lean_Expr_hasMVar(v_a_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3308_; 
lean_inc(v_a_3271_);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; 
v_unused_3309_ = lean_ctor_get(v___x_3270_, 0);
lean_dec(v_unused_3309_);
v___x_3274_ = v___x_3270_;
v_isShared_3275_ = v_isSharedCheck_3308_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___x_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3308_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v_cache_3277_; lean_object* v_mctx_3278_; lean_object* v_zetaDeltaFVarIds_3279_; lean_object* v_postponed_3280_; lean_object* v_diag_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3307_; 
v___x_3276_ = lean_st_ref_take(v_a_3091_);
v_cache_3277_ = lean_ctor_get(v___x_3276_, 1);
v_mctx_3278_ = lean_ctor_get(v___x_3276_, 0);
v_zetaDeltaFVarIds_3279_ = lean_ctor_get(v___x_3276_, 2);
v_postponed_3280_ = lean_ctor_get(v___x_3276_, 3);
v_diag_3281_ = lean_ctor_get(v___x_3276_, 4);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3283_ = v___x_3276_;
v_isShared_3284_ = v_isSharedCheck_3307_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_diag_3281_);
lean_inc(v_postponed_3280_);
lean_inc(v_zetaDeltaFVarIds_3279_);
lean_inc(v_cache_3277_);
lean_inc(v_mctx_3278_);
lean_dec(v___x_3276_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3307_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v_inferType_3285_; lean_object* v_funInfo_3286_; lean_object* v_synthInstance_3287_; lean_object* v_whnf_3288_; lean_object* v_defEqTrans_3289_; lean_object* v_defEqPerm_3290_; lean_object* v_isUnitLike_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3306_; 
v_inferType_3285_ = lean_ctor_get(v_cache_3277_, 0);
v_funInfo_3286_ = lean_ctor_get(v_cache_3277_, 1);
v_synthInstance_3287_ = lean_ctor_get(v_cache_3277_, 2);
v_whnf_3288_ = lean_ctor_get(v_cache_3277_, 3);
v_defEqTrans_3289_ = lean_ctor_get(v_cache_3277_, 4);
v_defEqPerm_3290_ = lean_ctor_get(v_cache_3277_, 5);
v_isUnitLike_3291_ = lean_ctor_get(v_cache_3277_, 6);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_cache_3277_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3293_ = v_cache_3277_;
v_isShared_3294_ = v_isSharedCheck_3306_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_isUnitLike_3291_);
lean_inc(v_defEqPerm_3290_);
lean_inc(v_defEqTrans_3289_);
lean_inc(v_whnf_3288_);
lean_inc(v_synthInstance_3287_);
lean_inc(v_funInfo_3286_);
lean_inc(v_inferType_3285_);
lean_dec(v_cache_3277_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3306_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_inc(v_a_3271_);
v___x_3295_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3285_, v_a_3265_, v_a_3271_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3295_);
v___x_3297_ = v___x_3293_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_funInfo_3286_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_synthInstance_3287_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_whnf_3288_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_defEqTrans_3289_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v_defEqPerm_3290_);
lean_ctor_set(v_reuseFailAlloc_3305_, 6, v_isUnitLike_3291_);
v___x_3297_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3297_);
v___x_3299_ = v___x_3283_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_mctx_3278_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_zetaDeltaFVarIds_3279_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_postponed_3280_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_diag_3281_);
v___x_3299_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_st_ref_put(v_a_3091_, v___x_3299_);
if (v_isShared_3275_ == 0)
{
v___x_3302_ = v___x_3274_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3271_);
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
}
}
}
else
{
lean_dec(v_a_3265_);
return v___x_3270_;
}
}
else
{
lean_dec(v_a_3265_);
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3241_);
v_a_3332_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3264_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3264_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3089_, 2);
goto v___jp_3247_;
}
}
v___jp_3247_:
{
lean_object* v_toCold_3248_; lean_object* v_cancelTk_x3f_3249_; 
v_toCold_3248_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3249_ = lean_ctor_get(v_toCold_3248_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3249_) == 1)
{
lean_object* v_val_3250_; uint8_t v___x_3251_; 
v_val_3250_ = lean_ctor_get(v_cancelTk_x3f_3249_, 0);
v___x_3251_ = l_IO_CancelToken_isSet(v_val_3250_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; 
v___x_3252_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3241_, v___x_3246_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec_ref(v___x_3246_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3241_);
v___x_3253_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3241_, v___x_3246_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec_ref(v___x_3246_);
return v___x_3262_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3340_; 
v_cacheInferType_3340_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3340_ == 0)
{
goto v___jp_3111_;
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = l_Lean_Expr_hasMVar(v_e_3089_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
lean_inc_ref(v_e_3089_);
v___x_3342_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3409_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3409_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3409_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3388_; lean_object* v_cache_3389_; lean_object* v_inferType_3390_; lean_object* v___x_3391_; 
v___x_3388_ = lean_st_ref_get(v_a_3091_);
v_cache_3389_ = lean_ctor_get(v___x_3388_, 1);
lean_inc_ref(v_cache_3389_);
lean_dec(v___x_3388_);
v_inferType_3390_ = lean_ctor_get(v_cache_3389_, 0);
lean_inc_ref(v_inferType_3390_);
lean_dec_ref(v_cache_3389_);
v___x_3391_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3390_, v_a_3343_);
lean_dec_ref(v_inferType_3390_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_toCold_3392_; lean_object* v_cancelTk_x3f_3393_; 
lean_del_object(v___x_3345_);
v_toCold_3392_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3393_ = lean_ctor_get(v_toCold_3392_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3393_) == 1)
{
lean_object* v_val_3394_; uint8_t v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_cancelTk_x3f_3393_, 0);
v___x_3395_ = l_IO_CancelToken_isSet(v_val_3394_);
if (v___x_3395_ == 0)
{
goto v___jp_3347_;
}
else
{
lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_a_3343_);
lean_dec_ref_known(v_e_3089_, 3);
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
goto v___jp_3347_;
}
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3407_; 
lean_dec(v_a_3343_);
lean_dec_ref_known(v_e_3089_, 3);
v_val_3405_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3391_, 1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v_val_3405_);
v___x_3407_ = v___x_3345_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_val_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
v___jp_3347_:
{
lean_object* v___x_3348_; 
v___x_3348_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; uint8_t v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v___x_3350_ = l_Lean_Expr_hasMVar(v_a_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3386_; 
lean_inc(v_a_3349_);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v___x_3348_, 0);
lean_dec(v_unused_3387_);
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3386_;
goto v_resetjp_3351_;
}
else
{
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3386_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v_cache_3355_; lean_object* v_mctx_3356_; lean_object* v_zetaDeltaFVarIds_3357_; lean_object* v_postponed_3358_; lean_object* v_diag_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3385_; 
v___x_3354_ = lean_st_ref_take(v_a_3091_);
v_cache_3355_ = lean_ctor_get(v___x_3354_, 1);
v_mctx_3356_ = lean_ctor_get(v___x_3354_, 0);
v_zetaDeltaFVarIds_3357_ = lean_ctor_get(v___x_3354_, 2);
v_postponed_3358_ = lean_ctor_get(v___x_3354_, 3);
v_diag_3359_ = lean_ctor_get(v___x_3354_, 4);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3361_ = v___x_3354_;
v_isShared_3362_ = v_isSharedCheck_3385_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_diag_3359_);
lean_inc(v_postponed_3358_);
lean_inc(v_zetaDeltaFVarIds_3357_);
lean_inc(v_cache_3355_);
lean_inc(v_mctx_3356_);
lean_dec(v___x_3354_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3385_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_inferType_3363_; lean_object* v_funInfo_3364_; lean_object* v_synthInstance_3365_; lean_object* v_whnf_3366_; lean_object* v_defEqTrans_3367_; lean_object* v_defEqPerm_3368_; lean_object* v_isUnitLike_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3384_; 
v_inferType_3363_ = lean_ctor_get(v_cache_3355_, 0);
v_funInfo_3364_ = lean_ctor_get(v_cache_3355_, 1);
v_synthInstance_3365_ = lean_ctor_get(v_cache_3355_, 2);
v_whnf_3366_ = lean_ctor_get(v_cache_3355_, 3);
v_defEqTrans_3367_ = lean_ctor_get(v_cache_3355_, 4);
v_defEqPerm_3368_ = lean_ctor_get(v_cache_3355_, 5);
v_isUnitLike_3369_ = lean_ctor_get(v_cache_3355_, 6);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_cache_3355_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3371_ = v_cache_3355_;
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_isUnitLike_3369_);
lean_inc(v_defEqPerm_3368_);
lean_inc(v_defEqTrans_3367_);
lean_inc(v_whnf_3366_);
lean_inc(v_synthInstance_3365_);
lean_inc(v_funInfo_3364_);
lean_inc(v_inferType_3363_);
lean_dec(v_cache_3355_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
lean_inc(v_a_3349_);
v___x_3373_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3363_, v_a_3343_, v_a_3349_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_funInfo_3364_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_synthInstance_3365_);
lean_ctor_set(v_reuseFailAlloc_3383_, 3, v_whnf_3366_);
lean_ctor_set(v_reuseFailAlloc_3383_, 4, v_defEqTrans_3367_);
lean_ctor_set(v_reuseFailAlloc_3383_, 5, v_defEqPerm_3368_);
lean_ctor_set(v_reuseFailAlloc_3383_, 6, v_isUnitLike_3369_);
v___x_3375_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 1, v___x_3375_);
v___x_3377_ = v___x_3361_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_mctx_3356_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_zetaDeltaFVarIds_3357_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_postponed_3358_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_diag_3359_);
v___x_3377_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3378_ = lean_st_ref_put(v_a_3091_, v___x_3377_);
if (v_isShared_3353_ == 0)
{
v___x_3380_ = v___x_3352_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3349_);
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
}
}
}
else
{
lean_dec(v_a_3343_);
return v___x_3348_;
}
}
else
{
lean_dec(v_a_3343_);
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref_known(v_e_3089_, 3);
v_a_3410_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3342_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3342_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
goto v___jp_3111_;
}
}
}
case 9:
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3418_ = lean_ctor_get(v_e_3089_, 0);
lean_inc_ref(v_a_3418_);
lean_dec_ref_known(v_e_3089_, 1);
v___x_3419_ = l_Lean_Literal_type(v_a_3418_);
lean_dec_ref(v_a_3418_);
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
case 10:
{
lean_object* v_expr_3421_; 
v_expr_3421_ = lean_ctor_get(v_e_3089_, 1);
lean_inc_ref(v_expr_3421_);
lean_dec_ref_known(v_e_3089_, 2);
v_e_3089_ = v_expr_3421_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3423_; lean_object* v_idx_3424_; lean_object* v_struct_3425_; uint8_t v_cacheInferType_3442_; 
v_typeName_3423_ = lean_ctor_get(v_e_3089_, 0);
lean_inc(v_typeName_3423_);
v_idx_3424_ = lean_ctor_get(v_e_3089_, 1);
lean_inc(v_idx_3424_);
v_struct_3425_ = lean_ctor_get(v_e_3089_, 2);
lean_inc_ref(v_struct_3425_);
v_cacheInferType_3442_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3442_ == 0)
{
lean_dec_ref_known(v_e_3089_, 3);
goto v___jp_3426_;
}
else
{
uint8_t v___x_3443_; 
v___x_3443_ = l_Lean_Expr_hasMVar(v_e_3089_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3511_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3511_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3511_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3490_; lean_object* v_cache_3491_; lean_object* v_inferType_3492_; lean_object* v___x_3493_; 
v___x_3490_ = lean_st_ref_get(v_a_3091_);
v_cache_3491_ = lean_ctor_get(v___x_3490_, 1);
lean_inc_ref(v_cache_3491_);
lean_dec(v___x_3490_);
v_inferType_3492_ = lean_ctor_get(v_cache_3491_, 0);
lean_inc_ref(v_inferType_3492_);
lean_dec_ref(v_cache_3491_);
v___x_3493_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3492_, v_a_3445_);
lean_dec_ref(v_inferType_3492_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_toCold_3494_; lean_object* v_cancelTk_x3f_3495_; 
lean_del_object(v___x_3447_);
v_toCold_3494_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3495_ = lean_ctor_get(v_toCold_3494_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3495_) == 1)
{
lean_object* v_val_3496_; uint8_t v___x_3497_; 
v_val_3496_ = lean_ctor_get(v_cancelTk_x3f_3495_, 0);
v___x_3497_ = l_IO_CancelToken_isSet(v_val_3496_);
if (v___x_3497_ == 0)
{
goto v___jp_3449_;
}
else
{
lean_object* v___x_3498_; lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_a_3445_);
lean_dec_ref(v_struct_3425_);
lean_dec(v_idx_3424_);
lean_dec(v_typeName_3423_);
v___x_3498_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
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
goto v___jp_3449_;
}
}
else
{
lean_object* v_val_3507_; lean_object* v___x_3509_; 
lean_dec(v_a_3445_);
lean_dec_ref(v_struct_3425_);
lean_dec(v_idx_3424_);
lean_dec(v_typeName_3423_);
v_val_3507_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_val_3507_);
lean_dec_ref_known(v___x_3493_, 1);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_val_3507_);
v___x_3509_ = v___x_3447_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_val_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
v___jp_3449_:
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3423_, v_idx_3424_, v_struct_3425_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; uint8_t v___x_3452_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v___x_3452_ = l_Lean_Expr_hasMVar(v_a_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3488_; 
lean_inc(v_a_3451_);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3489_);
v___x_3454_ = v___x_3450_;
v_isShared_3455_ = v_isSharedCheck_3488_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3488_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v_cache_3457_; lean_object* v_mctx_3458_; lean_object* v_zetaDeltaFVarIds_3459_; lean_object* v_postponed_3460_; lean_object* v_diag_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3487_; 
v___x_3456_ = lean_st_ref_take(v_a_3091_);
v_cache_3457_ = lean_ctor_get(v___x_3456_, 1);
v_mctx_3458_ = lean_ctor_get(v___x_3456_, 0);
v_zetaDeltaFVarIds_3459_ = lean_ctor_get(v___x_3456_, 2);
v_postponed_3460_ = lean_ctor_get(v___x_3456_, 3);
v_diag_3461_ = lean_ctor_get(v___x_3456_, 4);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3463_ = v___x_3456_;
v_isShared_3464_ = v_isSharedCheck_3487_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_diag_3461_);
lean_inc(v_postponed_3460_);
lean_inc(v_zetaDeltaFVarIds_3459_);
lean_inc(v_cache_3457_);
lean_inc(v_mctx_3458_);
lean_dec(v___x_3456_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3487_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_inferType_3465_; lean_object* v_funInfo_3466_; lean_object* v_synthInstance_3467_; lean_object* v_whnf_3468_; lean_object* v_defEqTrans_3469_; lean_object* v_defEqPerm_3470_; lean_object* v_isUnitLike_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3486_; 
v_inferType_3465_ = lean_ctor_get(v_cache_3457_, 0);
v_funInfo_3466_ = lean_ctor_get(v_cache_3457_, 1);
v_synthInstance_3467_ = lean_ctor_get(v_cache_3457_, 2);
v_whnf_3468_ = lean_ctor_get(v_cache_3457_, 3);
v_defEqTrans_3469_ = lean_ctor_get(v_cache_3457_, 4);
v_defEqPerm_3470_ = lean_ctor_get(v_cache_3457_, 5);
v_isUnitLike_3471_ = lean_ctor_get(v_cache_3457_, 6);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_cache_3457_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3473_ = v_cache_3457_;
v_isShared_3474_ = v_isSharedCheck_3486_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_isUnitLike_3471_);
lean_inc(v_defEqPerm_3470_);
lean_inc(v_defEqTrans_3469_);
lean_inc(v_whnf_3468_);
lean_inc(v_synthInstance_3467_);
lean_inc(v_funInfo_3466_);
lean_inc(v_inferType_3465_);
lean_dec(v_cache_3457_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3486_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_inc(v_a_3451_);
v___x_3475_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3465_, v_a_3445_, v_a_3451_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_funInfo_3466_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_synthInstance_3467_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_whnf_3468_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_defEqTrans_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 5, v_defEqPerm_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 6, v_isUnitLike_3471_);
v___x_3477_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___x_3477_);
v___x_3479_ = v___x_3463_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_mctx_3458_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_zetaDeltaFVarIds_3459_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_postponed_3460_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_diag_3461_);
v___x_3479_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = lean_st_ref_put(v_a_3091_, v___x_3479_);
if (v_isShared_3455_ == 0)
{
v___x_3482_ = v___x_3454_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3451_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3445_);
return v___x_3450_;
}
}
else
{
lean_dec(v_a_3445_);
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_struct_3425_);
lean_dec(v_idx_3424_);
lean_dec(v_typeName_3423_);
v_a_3512_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3444_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3444_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3089_, 3);
goto v___jp_3426_;
}
}
v___jp_3426_:
{
lean_object* v_toCold_3427_; lean_object* v_cancelTk_x3f_3428_; 
v_toCold_3427_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3428_ = lean_ctor_get(v_toCold_3427_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3428_) == 1)
{
lean_object* v_val_3429_; uint8_t v___x_3430_; 
v_val_3429_ = lean_ctor_get(v_cancelTk_x3f_3428_, 0);
v___x_3430_ = l_IO_CancelToken_isSet(v_val_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3423_, v_idx_3424_, v_struct_3425_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec_ref(v_struct_3425_);
lean_dec(v_idx_3424_);
lean_dec(v_typeName_3423_);
v___x_3432_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v___x_3441_; 
v___x_3441_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3423_, v_idx_3424_, v_struct_3425_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3441_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3520_; 
v_cacheInferType_3520_ = lean_ctor_get_uint8(v_a_3090_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3520_ == 0)
{
goto v___jp_3095_;
}
else
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Lean_Expr_hasMVar(v_e_3089_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_inc_ref(v_e_3089_);
v___x_3522_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3589_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3589_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3589_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3568_; lean_object* v_cache_3569_; lean_object* v_inferType_3570_; lean_object* v___x_3571_; 
v___x_3568_ = lean_st_ref_get(v_a_3091_);
v_cache_3569_ = lean_ctor_get(v___x_3568_, 1);
lean_inc_ref(v_cache_3569_);
lean_dec(v___x_3568_);
v_inferType_3570_ = lean_ctor_get(v_cache_3569_, 0);
lean_inc_ref(v_inferType_3570_);
lean_dec_ref(v_cache_3569_);
v___x_3571_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3570_, v_a_3523_);
lean_dec_ref(v_inferType_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_toCold_3572_; lean_object* v_cancelTk_x3f_3573_; 
lean_del_object(v___x_3525_);
v_toCold_3572_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3573_ = lean_ctor_get(v_toCold_3572_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3573_) == 1)
{
lean_object* v_val_3574_; uint8_t v___x_3575_; 
v_val_3574_ = lean_ctor_get(v_cancelTk_x3f_3573_, 0);
v___x_3575_ = l_IO_CancelToken_isSet(v_val_3574_);
if (v___x_3575_ == 0)
{
goto v___jp_3527_;
}
else
{
lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_a_3523_);
lean_dec_ref(v_e_3089_);
v___x_3576_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
goto v___jp_3527_;
}
}
else
{
lean_object* v_val_3585_; lean_object* v___x_3587_; 
lean_dec(v_a_3523_);
lean_dec_ref(v_e_3089_);
v_val_3585_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v___x_3571_, 1);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_val_3585_);
v___x_3587_ = v___x_3525_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_val_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
v___jp_3527_:
{
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; uint8_t v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v___x_3530_ = l_Lean_Expr_hasMVar(v_a_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3566_; 
lean_inc(v_a_3529_);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3528_, 0);
lean_dec(v_unused_3567_);
v___x_3532_ = v___x_3528_;
v_isShared_3533_ = v_isSharedCheck_3566_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v___x_3528_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3566_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v_cache_3535_; lean_object* v_mctx_3536_; lean_object* v_zetaDeltaFVarIds_3537_; lean_object* v_postponed_3538_; lean_object* v_diag_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3565_; 
v___x_3534_ = lean_st_ref_take(v_a_3091_);
v_cache_3535_ = lean_ctor_get(v___x_3534_, 1);
v_mctx_3536_ = lean_ctor_get(v___x_3534_, 0);
v_zetaDeltaFVarIds_3537_ = lean_ctor_get(v___x_3534_, 2);
v_postponed_3538_ = lean_ctor_get(v___x_3534_, 3);
v_diag_3539_ = lean_ctor_get(v___x_3534_, 4);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3541_ = v___x_3534_;
v_isShared_3542_ = v_isSharedCheck_3565_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_diag_3539_);
lean_inc(v_postponed_3538_);
lean_inc(v_zetaDeltaFVarIds_3537_);
lean_inc(v_cache_3535_);
lean_inc(v_mctx_3536_);
lean_dec(v___x_3534_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3565_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_inferType_3543_; lean_object* v_funInfo_3544_; lean_object* v_synthInstance_3545_; lean_object* v_whnf_3546_; lean_object* v_defEqTrans_3547_; lean_object* v_defEqPerm_3548_; lean_object* v_isUnitLike_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3564_; 
v_inferType_3543_ = lean_ctor_get(v_cache_3535_, 0);
v_funInfo_3544_ = lean_ctor_get(v_cache_3535_, 1);
v_synthInstance_3545_ = lean_ctor_get(v_cache_3535_, 2);
v_whnf_3546_ = lean_ctor_get(v_cache_3535_, 3);
v_defEqTrans_3547_ = lean_ctor_get(v_cache_3535_, 4);
v_defEqPerm_3548_ = lean_ctor_get(v_cache_3535_, 5);
v_isUnitLike_3549_ = lean_ctor_get(v_cache_3535_, 6);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_cache_3535_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3551_ = v_cache_3535_;
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_isUnitLike_3549_);
lean_inc(v_defEqPerm_3548_);
lean_inc(v_defEqTrans_3547_);
lean_inc(v_whnf_3546_);
lean_inc(v_synthInstance_3545_);
lean_inc(v_funInfo_3544_);
lean_inc(v_inferType_3543_);
lean_dec(v_cache_3535_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
lean_inc(v_a_3529_);
v___x_3553_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3543_, v_a_3523_, v_a_3529_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3555_ = v___x_3551_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_funInfo_3544_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_synthInstance_3545_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_whnf_3546_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_defEqTrans_3547_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_defEqPerm_3548_);
lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_isUnitLike_3549_);
v___x_3555_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v___x_3555_);
v___x_3557_ = v___x_3541_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_mctx_3536_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_zetaDeltaFVarIds_3537_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_postponed_3538_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v_diag_3539_);
v___x_3557_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_st_ref_put(v_a_3091_, v___x_3557_);
if (v_isShared_3533_ == 0)
{
v___x_3560_ = v___x_3532_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3529_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3523_);
return v___x_3528_;
}
}
else
{
lean_dec(v_a_3523_);
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_e_3089_);
v_a_3590_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3522_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3522_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
goto v___jp_3095_;
}
}
}
}
v___jp_3095_:
{
lean_object* v_toCold_3096_; lean_object* v_cancelTk_x3f_3097_; 
v_toCold_3096_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3097_ = lean_ctor_get(v_toCold_3096_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3097_) == 1)
{
lean_object* v_val_3098_; uint8_t v___x_3099_; 
v_val_3098_ = lean_ctor_get(v_cancelTk_x3f_3097_, 0);
v___x_3099_ = l_IO_CancelToken_isSet(v_val_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v_e_3089_);
v___x_3101_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3110_;
}
}
v___jp_3111_:
{
lean_object* v_toCold_3112_; lean_object* v_cancelTk_x3f_3113_; 
v_toCold_3112_ = lean_ctor_get(v_a_3092_, 0);
v_cancelTk_x3f_3113_ = lean_ctor_get(v_toCold_3112_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3113_) == 1)
{
lean_object* v_val_3114_; uint8_t v___x_3115_; 
v_val_3114_ = lean_ctor_get(v_cancelTk_x3f_3113_, 0);
v___x_3115_ = l_IO_CancelToken_isSet(v_val_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_e_3089_);
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
v___x_3126_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
return v___x_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3606_, v_x_3607_, v_x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3611_, v_x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3614_, v_x_3615_, v_x_3616_);
lean_dec_ref(v_x_3616_);
lean_dec_ref(v_x_3615_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3618_, lean_object* v_x_3619_, size_t v_x_3620_, size_t v_x_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3619_, v_x_3620_, v_x_3621_, v_x_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
size_t v_x_3676__boxed_3631_; size_t v_x_3677__boxed_3632_; lean_object* v_res_3633_; 
v_x_3676__boxed_3631_ = lean_unbox_usize(v_x_3627_);
lean_dec(v_x_3627_);
v_x_3677__boxed_3632_ = lean_unbox_usize(v_x_3628_);
lean_dec(v_x_3628_);
v_res_3633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3625_, v_x_3626_, v_x_3676__boxed_3631_, v_x_3677__boxed_3632_, v_x_3629_, v_x_3630_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3634_, lean_object* v_x_3635_, size_t v_x_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3635_, v_x_3636_, v_x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_){
_start:
{
size_t v_x_3693__boxed_3643_; lean_object* v_res_3644_; 
v_x_3693__boxed_3643_ = lean_unbox_usize(v_x_3641_);
lean_dec(v_x_3641_);
v_res_3644_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3639_, v_x_3640_, v_x_3693__boxed_3643_, v_x_3642_);
lean_dec_ref(v_x_3642_);
lean_dec_ref(v_x_3640_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3645_, lean_object* v_n_3646_, lean_object* v_k_3647_, lean_object* v_v_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3646_, v_k_3647_, v_v_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3650_, size_t v_depth_3651_, lean_object* v_keys_3652_, lean_object* v_vals_3653_, lean_object* v_heq_3654_, lean_object* v_i_3655_, lean_object* v_entries_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3651_, v_keys_3652_, v_vals_3653_, v_i_3655_, v_entries_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3658_, lean_object* v_depth_3659_, lean_object* v_keys_3660_, lean_object* v_vals_3661_, lean_object* v_heq_3662_, lean_object* v_i_3663_, lean_object* v_entries_3664_){
_start:
{
size_t v_depth_boxed_3665_; lean_object* v_res_3666_; 
v_depth_boxed_3665_ = lean_unbox_usize(v_depth_3659_);
lean_dec(v_depth_3659_);
v_res_3666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3658_, v_depth_boxed_3665_, v_keys_3660_, v_vals_3661_, v_heq_3662_, v_i_3663_, v_entries_3664_);
lean_dec_ref(v_vals_3661_);
lean_dec_ref(v_keys_3660_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3667_, lean_object* v_keys_3668_, lean_object* v_vals_3669_, lean_object* v_heq_3670_, lean_object* v_i_3671_, lean_object* v_k_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3668_, v_vals_3669_, v_i_3671_, v_k_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3674_, lean_object* v_keys_3675_, lean_object* v_vals_3676_, lean_object* v_heq_3677_, lean_object* v_i_3678_, lean_object* v_k_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3674_, v_keys_3675_, v_vals_3676_, v_heq_3677_, v_i_3678_, v_k_3679_);
lean_dec_ref(v_k_3679_);
lean_dec_ref(v_vals_3676_);
lean_dec_ref(v_keys_3675_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3682_, v_x_3683_, v_x_3684_, v_x_3685_);
return v___x_3686_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = l_Lean_maxRecDepthErrorMessage;
v___x_3693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3695_ = l_Lean_MessageData_ofFormat(v___x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3697_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3698_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3699_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v_ref_3699_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3707_, lean_object* v_ref_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3708_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_ref_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3715_, v_ref_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3775_; uint8_t v_beta_3776_; 
v___x_3775_ = l_Lean_Meta_Context_config(v___y_3724_);
v_beta_3776_ = lean_ctor_get_uint8(v___x_3775_, 13);
if (v_beta_3776_ == 0)
{
lean_dec_ref(v___x_3775_);
goto v___jp_3729_;
}
else
{
uint8_t v_iota_3777_; 
v_iota_3777_ = lean_ctor_get_uint8(v___x_3775_, 12);
if (v_iota_3777_ == 0)
{
lean_dec_ref(v___x_3775_);
goto v___jp_3729_;
}
else
{
uint8_t v_zeta_3778_; 
v_zeta_3778_ = lean_ctor_get_uint8(v___x_3775_, 15);
if (v_zeta_3778_ == 0)
{
lean_dec_ref(v___x_3775_);
goto v___jp_3729_;
}
else
{
uint8_t v_zetaHave_3779_; 
v_zetaHave_3779_ = lean_ctor_get_uint8(v___x_3775_, 18);
if (v_zetaHave_3779_ == 0)
{
lean_dec_ref(v___x_3775_);
goto v___jp_3729_;
}
else
{
uint8_t v_zetaDelta_3780_; 
v_zetaDelta_3780_ = lean_ctor_get_uint8(v___x_3775_, 16);
if (v_zetaDelta_3780_ == 0)
{
lean_dec_ref(v___x_3775_);
goto v___jp_3729_;
}
else
{
uint8_t v_etaStruct_3781_; uint8_t v_proj_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v_etaStruct_3781_ = lean_ctor_get_uint8(v___x_3775_, 10);
v_proj_3782_ = lean_ctor_get_uint8(v___x_3775_, 14);
lean_dec_ref(v___x_3775_);
v___x_3783_ = lean_box(v_proj_3782_);
v___x_3784_ = lean_obj_tag_nat(v___x_3783_);
lean_dec(v___x_3783_);
v___x_3785_ = lean_unsigned_to_nat(2u);
v___x_3786_ = lean_nat_dec_eq(v___x_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
goto v___jp_3729_;
}
else
{
uint8_t v___x_3787_; uint8_t v___x_3788_; 
v___x_3787_ = 0;
v___x_3788_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3781_, v___x_3787_);
if (v___x_3788_ == 0)
{
goto v___jp_3729_;
}
else
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec_ref(v___y_3724_);
return v___x_3789_;
}
}
}
}
}
}
}
v___jp_3729_:
{
lean_object* v___x_3730_; uint8_t v_foApprox_3731_; uint8_t v_ctxApprox_3732_; uint8_t v_quasiPatternApprox_3733_; uint8_t v_constApprox_3734_; uint8_t v_isDefEqStuckEx_3735_; uint8_t v_unificationHints_3736_; uint8_t v_proofIrrelevance_3737_; uint8_t v_assignSyntheticOpaque_3738_; uint8_t v_offsetCnstrs_3739_; uint8_t v_transparency_3740_; uint8_t v_univApprox_3741_; uint8_t v_zetaUnused_3742_; uint8_t v_canUnfoldPredicateConfig_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3774_; 
v___x_3730_ = l_Lean_Meta_Context_config(v___y_3724_);
v_foApprox_3731_ = lean_ctor_get_uint8(v___x_3730_, 0);
v_ctxApprox_3732_ = lean_ctor_get_uint8(v___x_3730_, 1);
v_quasiPatternApprox_3733_ = lean_ctor_get_uint8(v___x_3730_, 2);
v_constApprox_3734_ = lean_ctor_get_uint8(v___x_3730_, 3);
v_isDefEqStuckEx_3735_ = lean_ctor_get_uint8(v___x_3730_, 4);
v_unificationHints_3736_ = lean_ctor_get_uint8(v___x_3730_, 5);
v_proofIrrelevance_3737_ = lean_ctor_get_uint8(v___x_3730_, 6);
v_assignSyntheticOpaque_3738_ = lean_ctor_get_uint8(v___x_3730_, 7);
v_offsetCnstrs_3739_ = lean_ctor_get_uint8(v___x_3730_, 8);
v_transparency_3740_ = lean_ctor_get_uint8(v___x_3730_, 9);
v_univApprox_3741_ = lean_ctor_get_uint8(v___x_3730_, 11);
v_zetaUnused_3742_ = lean_ctor_get_uint8(v___x_3730_, 17);
v_canUnfoldPredicateConfig_3743_ = lean_ctor_get_uint8(v___x_3730_, 19);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3745_ = v___x_3730_;
v_isShared_3746_ = v_isSharedCheck_3774_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v___x_3730_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3774_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
uint8_t v___x_3747_; uint8_t v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3751_; 
v___x_3747_ = 1;
v___x_3748_ = 0;
v___x_3749_ = 2;
if (v_isShared_3746_ == 0)
{
v___x_3751_ = v___x_3745_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 0, v_foApprox_3731_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 1, v_ctxApprox_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 2, v_quasiPatternApprox_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 3, v_constApprox_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 4, v_isDefEqStuckEx_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 5, v_unificationHints_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 6, v_proofIrrelevance_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 7, v_assignSyntheticOpaque_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 8, v_offsetCnstrs_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 9, v_transparency_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 11, v_univApprox_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 17, v_zetaUnused_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3773_, 19, v_canUnfoldPredicateConfig_3743_);
v___x_3751_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
uint8_t v_trackZetaDelta_3752_; lean_object* v_zetaDeltaSet_3753_; lean_object* v_lctx_3754_; lean_object* v_localInstances_3755_; lean_object* v_defEqCtx_x3f_3756_; lean_object* v_synthPendingDepth_3757_; lean_object* v_customCanUnfoldPredicate_x3f_3758_; uint8_t v_univApprox_3759_; uint8_t v_inTypeClassResolution_3760_; uint8_t v_cacheInferType_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3771_; 
lean_ctor_set_uint8(v___x_3751_, 10, v___x_3748_);
lean_ctor_set_uint8(v___x_3751_, 12, v___x_3747_);
lean_ctor_set_uint8(v___x_3751_, 13, v___x_3747_);
lean_ctor_set_uint8(v___x_3751_, 14, v___x_3749_);
lean_ctor_set_uint8(v___x_3751_, 15, v___x_3747_);
lean_ctor_set_uint8(v___x_3751_, 16, v___x_3747_);
lean_ctor_set_uint8(v___x_3751_, 18, v___x_3747_);
v_trackZetaDelta_3752_ = lean_ctor_get_uint8(v___y_3724_, sizeof(void*)*7);
v_zetaDeltaSet_3753_ = lean_ctor_get(v___y_3724_, 1);
v_lctx_3754_ = lean_ctor_get(v___y_3724_, 2);
v_localInstances_3755_ = lean_ctor_get(v___y_3724_, 3);
v_defEqCtx_x3f_3756_ = lean_ctor_get(v___y_3724_, 4);
v_synthPendingDepth_3757_ = lean_ctor_get(v___y_3724_, 5);
v_customCanUnfoldPredicate_x3f_3758_ = lean_ctor_get(v___y_3724_, 6);
v_univApprox_3759_ = lean_ctor_get_uint8(v___y_3724_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3760_ = lean_ctor_get_uint8(v___y_3724_, sizeof(void*)*7 + 2);
v_cacheInferType_3761_ = lean_ctor_get_uint8(v___y_3724_, sizeof(void*)*7 + 3);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___y_3724_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___y_3724_, 0);
lean_dec(v_unused_3772_);
v___x_3763_ = v___y_3724_;
v_isShared_3764_ = v_isSharedCheck_3771_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3758_);
lean_inc(v_synthPendingDepth_3757_);
lean_inc(v_defEqCtx_x3f_3756_);
lean_inc(v_localInstances_3755_);
lean_inc(v_lctx_3754_);
lean_inc(v_zetaDeltaSet_3753_);
lean_dec(v___y_3724_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3771_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint64_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3765_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3751_);
v___x_3766_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3766_, 0, v___x_3751_);
lean_ctor_set_uint64(v___x_3766_, sizeof(void*)*1, v___x_3765_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_zetaDeltaSet_3753_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_lctx_3754_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_localInstances_3755_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_defEqCtx_x3f_3756_);
lean_ctor_set(v_reuseFailAlloc_3770_, 5, v_synthPendingDepth_3757_);
lean_ctor_set(v_reuseFailAlloc_3770_, 6, v_customCanUnfoldPredicate_x3f_3758_);
lean_ctor_set_uint8(v_reuseFailAlloc_3770_, sizeof(void*)*7, v_trackZetaDelta_3752_);
lean_ctor_set_uint8(v_reuseFailAlloc_3770_, sizeof(void*)*7 + 1, v_univApprox_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3770_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3760_);
lean_ctor_set_uint8(v_reuseFailAlloc_3770_, sizeof(void*)*7 + 3, v_cacheInferType_3761_);
v___x_3768_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3723_, v___x_3768_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec_ref(v___x_3768_);
return v___x_3769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___y_3804_; lean_object* v_toCold_3821_; lean_object* v_currRecDepth_3822_; lean_object* v_ref_3823_; uint16_t v_optionFlags_3824_; uint8_t v_suppressElabErrors_3825_; uint8_t v_checkDeprecated_3826_; uint8_t v_isRecordingDeps_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3867_; 
v_toCold_3821_ = lean_ctor_get(v_a_3800_, 0);
v_currRecDepth_3822_ = lean_ctor_get(v_a_3800_, 1);
v_ref_3823_ = lean_ctor_get(v_a_3800_, 2);
v_optionFlags_3824_ = lean_ctor_get_uint16(v_a_3800_, sizeof(void*)*3);
v_suppressElabErrors_3825_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*3 + 2);
v_checkDeprecated_3826_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3827_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*3 + 4);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3829_ = v_a_3800_;
v_isShared_3830_ = v_isSharedCheck_3867_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_ref_3823_);
lean_inc(v_currRecDepth_3822_);
lean_inc(v_toCold_3821_);
lean_dec(v_a_3800_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3867_;
goto v_resetjp_3828_;
}
v___jp_3803_:
{
if (lean_obj_tag(v___y_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
v_a_3805_ = lean_ctor_get(v___y_3804_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___y_3804_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___y_3804_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___y_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___y_3804_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___y_3804_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___y_3804_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___y_3804_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
v_resetjp_3828_:
{
lean_object* v_maxRecDepth_3831_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_maxRecDepth_3831_ = lean_ctor_get(v_toCold_3821_, 3);
v___x_3863_ = lean_unsigned_to_nat(0u);
v___x_3864_ = lean_nat_dec_eq(v_maxRecDepth_3831_, v___x_3863_);
if (v___x_3864_ == 0)
{
uint8_t v___x_3865_; 
v___x_3865_ = lean_nat_dec_eq(v_currRecDepth_3822_, v_maxRecDepth_3831_);
if (v___x_3865_ == 0)
{
goto v___jp_3832_;
}
else
{
lean_object* v___x_3866_; 
lean_del_object(v___x_3829_);
lean_dec(v_currRecDepth_3822_);
lean_dec_ref(v_toCold_3821_);
lean_dec(v_a_3801_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec_ref(v_e_3797_);
v___x_3866_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3823_);
return v___x_3866_;
}
}
else
{
goto v___jp_3832_;
}
v___jp_3832_:
{
lean_object* v___x_3833_; uint8_t v_transparency_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3833_ = l_Lean_Meta_Context_config(v_a_3798_);
v_transparency_3834_ = lean_ctor_get_uint8(v___x_3833_, 9);
lean_dec_ref(v___x_3833_);
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_nat_add(v_currRecDepth_3822_, v___x_3835_);
lean_dec(v_currRecDepth_3822_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v___x_3836_);
v___x_3838_ = v___x_3829_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_toCold_3821_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_ref_3823_);
lean_ctor_set_uint16(v_reuseFailAlloc_3862_, sizeof(void*)*3, v_optionFlags_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3862_, sizeof(void*)*3 + 2, v_suppressElabErrors_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3862_, sizeof(void*)*3 + 3, v_checkDeprecated_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3862_, sizeof(void*)*3 + 4, v_isRecordingDeps_3827_);
v___x_3838_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
uint8_t v___x_3839_; uint8_t v___x_3840_; 
v___x_3839_ = 1;
v___x_3840_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3834_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3797_, v_a_3798_, v_a_3799_, v___x_3838_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v___x_3838_);
lean_dec(v_a_3799_);
v___y_3804_ = v___x_3841_;
goto v___jp_3803_;
}
else
{
lean_object* v_keyedConfig_3842_; uint8_t v_trackZetaDelta_3843_; lean_object* v_zetaDeltaSet_3844_; lean_object* v_lctx_3845_; lean_object* v_localInstances_3846_; lean_object* v_defEqCtx_x3f_3847_; lean_object* v_synthPendingDepth_3848_; lean_object* v_customCanUnfoldPredicate_x3f_3849_; uint8_t v_univApprox_3850_; uint8_t v_inTypeClassResolution_3851_; uint8_t v_cacheInferType_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3861_; 
v_keyedConfig_3842_ = lean_ctor_get(v_a_3798_, 0);
v_trackZetaDelta_3843_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7);
v_zetaDeltaSet_3844_ = lean_ctor_get(v_a_3798_, 1);
v_lctx_3845_ = lean_ctor_get(v_a_3798_, 2);
v_localInstances_3846_ = lean_ctor_get(v_a_3798_, 3);
v_defEqCtx_x3f_3847_ = lean_ctor_get(v_a_3798_, 4);
v_synthPendingDepth_3848_ = lean_ctor_get(v_a_3798_, 5);
v_customCanUnfoldPredicate_x3f_3849_ = lean_ctor_get(v_a_3798_, 6);
v_univApprox_3850_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3851_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 2);
v_cacheInferType_3852_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 3);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3854_ = v_a_3798_;
v_isShared_3855_ = v_isSharedCheck_3861_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3849_);
lean_inc(v_synthPendingDepth_3848_);
lean_inc(v_defEqCtx_x3f_3847_);
lean_inc(v_localInstances_3846_);
lean_inc(v_lctx_3845_);
lean_inc(v_zetaDeltaSet_3844_);
lean_inc(v_keyedConfig_3842_);
lean_dec(v_a_3798_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3861_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3839_, v_keyedConfig_3842_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_zetaDeltaSet_3844_);
lean_ctor_set(v_reuseFailAlloc_3860_, 2, v_lctx_3845_);
lean_ctor_set(v_reuseFailAlloc_3860_, 3, v_localInstances_3846_);
lean_ctor_set(v_reuseFailAlloc_3860_, 4, v_defEqCtx_x3f_3847_);
lean_ctor_set(v_reuseFailAlloc_3860_, 5, v_synthPendingDepth_3848_);
lean_ctor_set(v_reuseFailAlloc_3860_, 6, v_customCanUnfoldPredicate_x3f_3849_);
lean_ctor_set_uint8(v_reuseFailAlloc_3860_, sizeof(void*)*7, v_trackZetaDelta_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3860_, sizeof(void*)*7 + 1, v_univApprox_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3860_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3851_);
lean_ctor_set_uint8(v_reuseFailAlloc_3860_, sizeof(void*)*7 + 3, v_cacheInferType_3852_);
v___x_3858_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3797_, v___x_3858_, v_a_3799_, v___x_3838_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v___x_3838_);
lean_dec(v_a_3799_);
v___y_3804_ = v___x_3859_;
goto v___jp_3803_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = lean_infer_type(v_e_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3875_){
_start:
{
switch(lean_obj_tag(v_x_3875_))
{
case 0:
{
uint8_t v___x_3876_; 
v___x_3876_ = 1;
return v___x_3876_;
}
case 2:
{
lean_object* v_a_3877_; lean_object* v_a_3878_; uint8_t v___x_3879_; 
v_a_3877_ = lean_ctor_get(v_x_3875_, 0);
v_a_3878_ = lean_ctor_get(v_x_3875_, 1);
v___x_3879_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3877_);
if (v___x_3879_ == 0)
{
return v___x_3879_;
}
else
{
v_x_3875_ = v_a_3878_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3881_; 
v_a_3881_ = lean_ctor_get(v_x_3875_, 1);
v_x_3875_ = v_a_3881_;
goto _start;
}
default: 
{
uint8_t v___x_3883_; 
v___x_3883_ = 0;
return v___x_3883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3884_){
_start:
{
uint8_t v_res_3885_; lean_object* v_r_3886_; 
v_res_3885_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3884_);
lean_dec(v_x_3884_);
v_r_3886_ = lean_box(v_res_3885_);
return v_r_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; lean_object* v_mctx_3891_; lean_object* v___x_3892_; lean_object* v_fst_3893_; lean_object* v_snd_3894_; lean_object* v___x_3895_; lean_object* v_cache_3896_; lean_object* v_zetaDeltaFVarIds_3897_; lean_object* v_postponed_3898_; lean_object* v_diag_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3908_; 
v___x_3890_ = lean_st_ref_get(v___y_3888_);
v_mctx_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc_ref(v_mctx_3891_);
lean_dec(v___x_3890_);
v___x_3892_ = lean_instantiate_level_mvars(v_mctx_3891_, v_l_3887_);
v_fst_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_fst_3893_);
v_snd_3894_ = lean_ctor_get(v___x_3892_, 1);
lean_inc(v_snd_3894_);
lean_dec_ref(v___x_3892_);
v___x_3895_ = lean_st_ref_take(v___y_3888_);
v_cache_3896_ = lean_ctor_get(v___x_3895_, 1);
v_zetaDeltaFVarIds_3897_ = lean_ctor_get(v___x_3895_, 2);
v_postponed_3898_ = lean_ctor_get(v___x_3895_, 3);
v_diag_3899_ = lean_ctor_get(v___x_3895_, 4);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; 
v_unused_3909_ = lean_ctor_get(v___x_3895_, 0);
lean_dec(v_unused_3909_);
v___x_3901_ = v___x_3895_;
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_diag_3899_);
lean_inc(v_postponed_3898_);
lean_inc(v_zetaDeltaFVarIds_3897_);
lean_inc(v_cache_3896_);
lean_dec(v___x_3895_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v_fst_3893_);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_fst_3893_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_cache_3896_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_zetaDeltaFVarIds_3897_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_postponed_3898_);
lean_ctor_set(v_reuseFailAlloc_3907_, 4, v_diag_3899_);
v___x_3904_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_st_ref_put(v___y_3888_, v___x_3904_);
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_snd_3894_);
return v___x_3906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3910_, v___y_3911_);
lean_dec(v___y_3911_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3914_, v___y_3916_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_00_u03c3_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v___y_3941_; 
switch(lean_obj_tag(v_x_3929_))
{
case 3:
{
lean_object* v_u_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_u_3962_ = lean_ctor_get(v_x_3929_, 0);
lean_inc(v_u_3962_);
lean_dec_ref_known(v_x_3929_, 1);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_nat_dec_eq(v_x_3930_, v___x_3963_);
lean_dec(v_x_3930_);
if (v___x_3964_ == 0)
{
lean_dec(v_u_3962_);
lean_dec_ref(v_00_u03c3_3928_);
goto v___jp_3936_;
}
else
{
lean_object* v_paramNames_3965_; lean_object* v_lvls_3966_; uint8_t v___x_3967_; 
v_paramNames_3965_ = lean_ctor_get(v_00_u03c3_3928_, 0);
lean_inc(v_paramNames_3965_);
v_lvls_3966_ = lean_ctor_get(v_00_u03c3_3928_, 1);
lean_inc(v_lvls_3966_);
lean_dec_ref(v_00_u03c3_3928_);
v___x_3967_ = l_List_isEmpty___redArg(v_paramNames_3965_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_Level_instantiateParams(v_u_3962_, v_paramNames_3965_, v_lvls_3966_);
v___y_3941_ = v___x_3968_;
goto v___jp_3940_;
}
else
{
lean_dec(v_lvls_3966_);
lean_dec(v_paramNames_3965_);
v___y_3941_ = v_u_3962_;
goto v___jp_3940_;
}
}
}
case 7:
{
lean_object* v_body_3969_; lean_object* v_zero_3970_; uint8_t v_isZero_3971_; 
v_body_3969_ = lean_ctor_get(v_x_3929_, 2);
lean_inc_ref(v_body_3969_);
lean_dec_ref_known(v_x_3929_, 3);
v_zero_3970_ = lean_unsigned_to_nat(0u);
v_isZero_3971_ = lean_nat_dec_eq(v_x_3930_, v_zero_3970_);
if (v_isZero_3971_ == 1)
{
uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v_body_3969_);
lean_dec(v_x_3930_);
lean_dec_ref(v_00_u03c3_3928_);
v___x_3972_ = 0;
v___x_3973_ = lean_box(v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
else
{
lean_object* v_one_3975_; lean_object* v_n_3976_; 
v_one_3975_ = lean_unsigned_to_nat(1u);
v_n_3976_ = lean_nat_sub(v_x_3930_, v_one_3975_);
lean_dec(v_x_3930_);
v_x_3929_ = v_body_3969_;
v_x_3930_ = v_n_3976_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3978_; 
v_body_3978_ = lean_ctor_get(v_x_3929_, 3);
lean_inc_ref(v_body_3978_);
lean_dec_ref_known(v_x_3929_, 4);
v_x_3929_ = v_body_3978_;
goto _start;
}
case 10:
{
lean_object* v_expr_3980_; 
v_expr_3980_ = lean_ctor_get(v_x_3929_, 1);
lean_inc_ref(v_expr_3980_);
lean_dec_ref_known(v_x_3929_, 2);
v_x_3929_ = v_expr_3980_;
goto _start;
}
default: 
{
lean_dec(v_x_3930_);
lean_dec_ref(v_x_3929_);
lean_dec_ref(v_00_u03c3_3928_);
goto v___jp_3936_;
}
}
v___jp_3936_:
{
uint8_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3937_ = 2;
v___x_3938_ = lean_box(v___x_3937_);
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
v___jp_3940_:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v___y_3941_, v_a_3932_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3953_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3953_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3953_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
uint8_t v___x_3947_; uint8_t v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3943_);
lean_dec(v_a_3943_);
v___x_3948_ = l_Lean_Bool_toLBool(v___x_3947_);
v___x_3949_ = lean_box(v___x_3948_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3949_);
v___x_3951_ = v___x_3945_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
v_a_3954_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3942_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3942_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_00_u03c3_3982_, lean_object* v_x_3983_, lean_object* v_x_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_00_u03c3_3982_, v_x_3983_, v_x_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object* v_00_u03c3_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
if (lean_obj_tag(v_a_3992_) == 0)
{
lean_object* v___x_3994_; 
lean_dec_ref(v_00_u03c3_3991_);
v___x_3994_ = l_List_reverse___redArg(v_a_3993_);
return v___x_3994_;
}
else
{
lean_object* v_head_3995_; lean_object* v_tail_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4010_; 
v_head_3995_ = lean_ctor_get(v_a_3992_, 0);
v_tail_3996_ = lean_ctor_get(v_a_3992_, 1);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3992_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3998_ = v_a_3992_;
v_isShared_3999_ = v_isSharedCheck_4010_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_tail_3996_);
lean_inc(v_head_3995_);
lean_dec(v_a_3992_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4010_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___y_4001_; lean_object* v_paramNames_4006_; lean_object* v_lvls_4007_; uint8_t v___x_4008_; 
v_paramNames_4006_ = lean_ctor_get(v_00_u03c3_3991_, 0);
v_lvls_4007_ = lean_ctor_get(v_00_u03c3_3991_, 1);
v___x_4008_ = l_List_isEmpty___redArg(v_paramNames_4006_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; 
lean_inc(v_lvls_4007_);
lean_inc(v_paramNames_4006_);
v___x_4009_ = l_Lean_Level_instantiateParams(v_head_3995_, v_paramNames_4006_, v_lvls_4007_);
v___y_4001_ = v___x_4009_;
goto v___jp_4000_;
}
else
{
v___y_4001_ = v_head_3995_;
goto v___jp_4000_;
}
v___jp_4000_:
{
lean_object* v___x_4003_; 
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 1, v_a_3993_);
lean_ctor_set(v___x_3998_, 0, v___y_4001_);
v___x_4003_ = v___x_3998_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___y_4001_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_3993_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
v_a_3992_ = v_tail_3996_;
v_a_3993_ = v___x_4003_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_00_u03c3_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
switch(lean_obj_tag(v_x_4014_))
{
case 4:
{
lean_object* v_declName_4021_; lean_object* v_us_4022_; lean_object* v___y_4024_; lean_object* v_paramNames_4038_; uint8_t v___x_4039_; 
v_declName_4021_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_declName_4021_);
v_us_4022_ = lean_ctor_get(v_x_4014_, 1);
lean_inc(v_us_4022_);
lean_dec_ref_known(v_x_4014_, 2);
v_paramNames_4038_ = lean_ctor_get(v_00_u03c3_4013_, 0);
v___x_4039_ = l_List_isEmpty___redArg(v_paramNames_4038_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_box(0);
v___x_4041_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4013_, v_us_4022_, v___x_4040_);
v___y_4024_ = v___x_4041_;
goto v___jp_4023_;
}
else
{
lean_dec_ref(v_00_u03c3_4013_);
v___y_4024_ = v_us_4022_;
goto v___jp_4023_;
}
v___jp_4023_:
{
lean_object* v___x_4025_; 
v___x_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4021_, v___y_4024_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v_fst_4027_; lean_object* v_snd_4028_; lean_object* v___x_4029_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v_fst_4027_ = lean_ctor_get(v_a_4026_, 0);
lean_inc(v_fst_4027_);
v_snd_4028_ = lean_ctor_get(v_a_4026_, 1);
lean_inc(v_snd_4028_);
lean_dec(v_a_4026_);
v___x_4029_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4028_, v_fst_4027_, v_x_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4029_;
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_x_4015_);
v_a_4030_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4025_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4025_);
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
}
case 1:
{
lean_object* v_fvarId_4042_; lean_object* v___x_4043_; 
lean_dec_ref(v_00_u03c3_4013_);
v_fvarId_4042_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_fvarId_4042_);
lean_dec_ref_known(v_x_4014_, 1);
v___x_4043_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4042_, v_a_4016_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4046_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4045_, v_a_4044_, v_x_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4046_;
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_x_4015_);
v_a_4047_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4043_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4043_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4055_; lean_object* v___x_4056_; 
lean_dec_ref(v_00_u03c3_4013_);
v_mvarId_4055_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_mvarId_4055_);
lean_dec_ref_known(v_x_4014_, 1);
v___x_4056_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4055_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4059_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4058_, v_a_4057_, v_x_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4059_;
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v_x_4015_);
v_a_4060_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4056_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4056_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
case 5:
{
lean_object* v_fn_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_fn_4068_ = lean_ctor_get(v_x_4014_, 0);
lean_inc_ref(v_fn_4068_);
lean_dec_ref_known(v_x_4014_, 2);
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_nat_add(v_x_4015_, v___x_4069_);
lean_dec(v_x_4015_);
v_x_4014_ = v_fn_4068_;
v_x_4015_ = v___x_4070_;
goto _start;
}
case 10:
{
lean_object* v_expr_4072_; 
v_expr_4072_ = lean_ctor_get(v_x_4014_, 1);
lean_inc_ref(v_expr_4072_);
lean_dec_ref_known(v_x_4014_, 2);
v_x_4014_ = v_expr_4072_;
goto _start;
}
case 8:
{
lean_object* v_body_4074_; 
v_body_4074_ = lean_ctor_get(v_x_4014_, 3);
lean_inc_ref(v_body_4074_);
lean_dec_ref_known(v_x_4014_, 4);
v_x_4014_ = v_body_4074_;
goto _start;
}
case 6:
{
lean_object* v_body_4076_; lean_object* v_zero_4077_; uint8_t v_isZero_4078_; 
v_body_4076_ = lean_ctor_get(v_x_4014_, 2);
lean_inc_ref(v_body_4076_);
lean_dec_ref_known(v_x_4014_, 3);
v_zero_4077_ = lean_unsigned_to_nat(0u);
v_isZero_4078_ = lean_nat_dec_eq(v_x_4015_, v_zero_4077_);
if (v_isZero_4078_ == 1)
{
uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec_ref(v_body_4076_);
lean_dec(v_x_4015_);
lean_dec_ref(v_00_u03c3_4013_);
v___x_4079_ = 0;
v___x_4080_ = lean_box(v___x_4079_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
else
{
lean_object* v_one_4082_; lean_object* v_n_4083_; 
v_one_4082_ = lean_unsigned_to_nat(1u);
v_n_4083_ = lean_nat_sub(v_x_4015_, v_one_4082_);
lean_dec(v_x_4015_);
v_x_4014_ = v_body_4076_;
v_x_4015_ = v_n_4083_;
goto _start;
}
}
default: 
{
uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec(v_x_4015_);
lean_dec_ref(v_x_4014_);
lean_dec_ref(v_00_u03c3_4013_);
v___x_4085_ = 2;
v___x_4086_ = lean_box(v___x_4085_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
return v___x_4087_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_00_u03c3_4088_, lean_object* v_x_4089_, lean_object* v_x_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4088_, v_x_4089_, v_x_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object* v_00_u03c3_4097_, lean_object* v_x_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
switch(lean_obj_tag(v_x_4098_))
{
case 1:
{
lean_object* v_fvarId_4104_; lean_object* v___x_4105_; 
lean_dec_ref(v_00_u03c3_4097_);
v_fvarId_4104_ = lean_ctor_get(v_x_4098_, 0);
lean_inc(v_fvarId_4104_);
lean_dec_ref_known(v_x_4098_, 1);
v___x_4105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4104_, v_a_4099_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v___x_4107_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4107_, v_a_4106_, v___x_4108_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4109_;
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_a_4110_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4105_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4105_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4118_; lean_object* v___x_4119_; 
lean_dec_ref(v_00_u03c3_4097_);
v_mvarId_4118_ = lean_ctor_get(v_x_4098_, 0);
lean_inc(v_mvarId_4118_);
lean_dec_ref_known(v_x_4098_, 1);
v___x_4119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4118_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4121_, v_a_4120_, v___x_4122_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4123_;
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v_a_4124_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4119_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4119_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
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
case 3:
{
uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_dec_ref_known(v_x_4098_, 1);
lean_dec_ref(v_00_u03c3_4097_);
v___x_4132_ = 0;
v___x_4133_ = lean_box(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
case 4:
{
lean_object* v_declName_4135_; lean_object* v_us_4136_; lean_object* v___y_4138_; lean_object* v_paramNames_4153_; uint8_t v___x_4154_; 
v_declName_4135_ = lean_ctor_get(v_x_4098_, 0);
lean_inc(v_declName_4135_);
v_us_4136_ = lean_ctor_get(v_x_4098_, 1);
lean_inc(v_us_4136_);
lean_dec_ref_known(v_x_4098_, 2);
v_paramNames_4153_ = lean_ctor_get(v_00_u03c3_4097_, 0);
v___x_4154_ = l_List_isEmpty___redArg(v_paramNames_4153_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_box(0);
v___x_4156_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4097_, v_us_4136_, v___x_4155_);
v___y_4138_ = v___x_4156_;
goto v___jp_4137_;
}
else
{
lean_dec_ref(v_00_u03c3_4097_);
v___y_4138_ = v_us_4136_;
goto v___jp_4137_;
}
v___jp_4137_:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4135_, v___y_4138_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v_fst_4141_; lean_object* v_snd_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v_fst_4141_ = lean_ctor_get(v_a_4140_, 0);
lean_inc(v_fst_4141_);
v_snd_4142_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_snd_4142_);
lean_dec(v_a_4140_);
v___x_4143_ = lean_unsigned_to_nat(0u);
v___x_4144_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4142_, v_fst_4141_, v___x_4143_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
v_a_4145_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4139_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4139_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_fn_4157_ = lean_ctor_get(v_x_4098_, 0);
lean_inc_ref(v_fn_4157_);
lean_dec_ref_known(v_x_4098_, 2);
v___x_4158_ = lean_unsigned_to_nat(1u);
v___x_4159_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4097_, v_fn_4157_, v___x_4158_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4159_;
}
case 6:
{
uint8_t v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec_ref_known(v_x_4098_, 3);
lean_dec_ref(v_00_u03c3_4097_);
v___x_4160_ = 0;
v___x_4161_ = lean_box(v___x_4160_);
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
case 7:
{
lean_object* v_body_4163_; 
v_body_4163_ = lean_ctor_get(v_x_4098_, 2);
lean_inc_ref(v_body_4163_);
lean_dec_ref_known(v_x_4098_, 3);
v_x_4098_ = v_body_4163_;
goto _start;
}
case 8:
{
lean_object* v_body_4165_; 
v_body_4165_ = lean_ctor_get(v_x_4098_, 3);
lean_inc_ref(v_body_4165_);
lean_dec_ref_known(v_x_4098_, 4);
v_x_4098_ = v_body_4165_;
goto _start;
}
case 9:
{
uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec_ref_known(v_x_4098_, 1);
lean_dec_ref(v_00_u03c3_4097_);
v___x_4167_ = 0;
v___x_4168_ = lean_box(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
case 10:
{
lean_object* v_expr_4170_; 
v_expr_4170_ = lean_ctor_get(v_x_4098_, 1);
lean_inc_ref(v_expr_4170_);
lean_dec_ref_known(v_x_4098_, 2);
v_x_4098_ = v_expr_4170_;
goto _start;
}
default: 
{
uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec_ref(v_x_4098_);
lean_dec_ref(v_00_u03c3_4097_);
v___x_4172_ = 2;
v___x_4173_ = lean_box(v___x_4172_);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object* v_00_u03c3_4175_, lean_object* v_x_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4175_, v_x_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_e_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v___x_4189_, v_e_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_e_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_Meta_isPropQuick(v_e_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4204_; 
lean_inc_ref(v_e_4198_);
v___x_4204_ = l_Lean_Meta_isPropQuick(v_e_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4261_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4261_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4261_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
uint8_t v___x_4209_; 
v___x_4209_ = lean_unbox(v_a_4205_);
lean_dec(v_a_4205_);
switch(v___x_4209_)
{
case 0:
{
uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
lean_dec_ref(v_e_4198_);
v___x_4210_ = 0;
v___x_4211_ = lean_box(v___x_4210_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4211_);
v___x_4213_ = v___x_4207_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
case 1:
{
uint8_t v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4218_; 
lean_dec_ref(v_e_4198_);
v___x_4215_ = 1;
v___x_4216_ = lean_box(v___x_4215_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4216_);
v___x_4218_ = v___x_4207_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
default: 
{
lean_object* v___x_4220_; 
lean_del_object(v___x_4207_);
lean_inc(v_a_4202_);
lean_inc_ref(v_a_4201_);
lean_inc(v_a_4200_);
lean_inc_ref(v_a_4199_);
v___x_4220_ = lean_infer_type(v_e_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = l_Lean_Meta_whnfD(v_a_4221_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4244_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4244_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4244_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
if (lean_obj_tag(v_a_4223_) == 3)
{
lean_object* v_u_4227_; lean_object* v___x_4228_; lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4238_; 
lean_del_object(v___x_4225_);
v_u_4227_ = lean_ctor_get(v_a_4223_, 0);
lean_inc(v_u_4227_);
lean_dec_ref_known(v_a_4223_, 1);
v___x_4228_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4227_, v_a_4200_);
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4238_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4238_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4233_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4229_);
lean_dec(v_a_4229_);
v___x_4234_ = lean_box(v___x_4233_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4234_);
v___x_4236_ = v___x_4231_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
else
{
uint8_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4242_; 
lean_dec(v_a_4223_);
v___x_4239_ = 0;
v___x_4240_ = lean_box(v___x_4239_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4240_);
v___x_4242_ = v___x_4225_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
v_a_4245_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4222_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4222_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
v_a_4253_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4220_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4220_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v_e_4198_);
v_a_4262_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4204_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4204_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Meta_isProp(v_e_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = lean_obj_tag_nat(v_x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4279_);
lean_dec(v_x_4279_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4281_, lean_object* v_k_4282_){
_start:
{
if (lean_obj_tag(v_t_4281_) == 3)
{
lean_object* v_idx_4283_; lean_object* v_numArgs_4284_; lean_object* v___x_4285_; 
v_idx_4283_ = lean_ctor_get(v_t_4281_, 0);
lean_inc(v_idx_4283_);
v_numArgs_4284_ = lean_ctor_get(v_t_4281_, 1);
lean_inc(v_numArgs_4284_);
lean_dec_ref_known(v_t_4281_, 2);
v___x_4285_ = lean_apply_2(v_k_4282_, v_idx_4283_, v_numArgs_4284_);
return v___x_4285_;
}
else
{
lean_dec(v_t_4281_);
return v_k_4282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4286_, lean_object* v_ctorIdx_4287_, lean_object* v_t_4288_, lean_object* v_h_4289_, lean_object* v_k_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4288_, v_k_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4292_, lean_object* v_ctorIdx_4293_, lean_object* v_t_4294_, lean_object* v_h_4295_, lean_object* v_k_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4292_, v_ctorIdx_4293_, v_t_4294_, v_h_4295_, v_k_4296_);
lean_dec(v_ctorIdx_4293_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4298_, lean_object* v_false_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4298_, v_false_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4301_, lean_object* v_t_4302_, lean_object* v_h_4303_, lean_object* v_false_4304_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4302_, v_false_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4306_, lean_object* v_true_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4306_, v_true_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4309_, lean_object* v_t_4310_, lean_object* v_h_4311_, lean_object* v_true_4312_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4310_, v_true_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4314_, lean_object* v_undef_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4314_, v_undef_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4317_, lean_object* v_t_4318_, lean_object* v_h_4319_, lean_object* v_undef_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4318_, v_undef_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4322_, lean_object* v_bvar_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4322_, v_bvar_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4325_, lean_object* v_t_4326_, lean_object* v_h_4327_, lean_object* v_bvar_4328_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4326_, v_bvar_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4330_){
_start:
{
switch(v_x_4330_)
{
case 0:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_box(0);
return v___x_4331_;
}
case 1:
{
lean_object* v___x_4332_; 
v___x_4332_ = lean_box(1);
return v___x_4332_;
}
default: 
{
lean_object* v___x_4333_; 
v___x_4333_ = lean_box(2);
return v___x_4333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4334_){
_start:
{
uint8_t v_x_25__boxed_4335_; lean_object* v_res_4336_; 
v_x_25__boxed_4335_ = lean_unbox(v_x_4334_);
v_res_4336_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4335_);
return v_res_4336_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4337_){
_start:
{
switch(lean_obj_tag(v_x_4337_))
{
case 0:
{
uint8_t v___x_4338_; 
v___x_4338_ = 0;
return v___x_4338_;
}
case 1:
{
uint8_t v___x_4339_; 
v___x_4339_ = 1;
return v___x_4339_;
}
default: 
{
uint8_t v___x_4340_; 
v___x_4340_ = 2;
return v___x_4340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4341_){
_start:
{
uint8_t v_res_4342_; lean_object* v_r_4343_; 
v_res_4342_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4341_);
lean_dec(v_x_4341_);
v_r_4343_ = lean_box(v_res_4342_);
return v_r_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_00_u03c3_4345_, lean_object* v_e_4346_, lean_object* v_numArgs_4347_){
_start:
{
lean_object* v___y_4349_; 
switch(lean_obj_tag(v_e_4346_))
{
case 3:
{
lean_object* v_u_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v_u_4355_ = lean_ctor_get(v_e_4346_, 0);
lean_inc(v_u_4355_);
lean_dec_ref_known(v_e_4346_, 1);
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = lean_nat_dec_eq(v_numArgs_4347_, v___x_4356_);
lean_dec(v_numArgs_4347_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; 
lean_dec(v_u_4355_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4358_ = lean_box(2);
return v___x_4358_;
}
else
{
lean_object* v_paramNames_4359_; lean_object* v_lvls_4360_; uint8_t v___x_4361_; 
v_paramNames_4359_ = lean_ctor_get(v_00_u03c3_4345_, 0);
lean_inc(v_paramNames_4359_);
v_lvls_4360_ = lean_ctor_get(v_00_u03c3_4345_, 1);
lean_inc(v_lvls_4360_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4361_ = l_List_isEmpty___redArg(v_paramNames_4359_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Level_instantiateParams(v_u_4355_, v_paramNames_4359_, v_lvls_4360_);
v___y_4349_ = v___x_4362_;
goto v___jp_4348_;
}
else
{
lean_dec(v_lvls_4360_);
lean_dec(v_paramNames_4359_);
v___y_4349_ = v_u_4355_;
goto v___jp_4348_;
}
}
}
case 7:
{
lean_object* v_body_4363_; lean_object* v_zero_4364_; uint8_t v_isZero_4365_; 
v_body_4363_ = lean_ctor_get(v_e_4346_, 2);
lean_inc_ref(v_body_4363_);
lean_dec_ref_known(v_e_4346_, 3);
v_zero_4364_ = lean_unsigned_to_nat(0u);
v_isZero_4365_ = lean_nat_dec_eq(v_numArgs_4347_, v_zero_4364_);
if (v_isZero_4365_ == 0)
{
lean_object* v_one_4366_; lean_object* v_n_4367_; 
v_one_4366_ = lean_unsigned_to_nat(1u);
v_n_4367_ = lean_nat_sub(v_numArgs_4347_, v_one_4366_);
lean_dec(v_numArgs_4347_);
v_e_4346_ = v_body_4363_;
v_numArgs_4347_ = v_n_4367_;
goto _start;
}
else
{
lean_object* v___x_4369_; 
lean_dec_ref(v_body_4363_);
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4369_ = lean_box(2);
return v___x_4369_;
}
}
case 10:
{
lean_object* v_expr_4370_; 
v_expr_4370_ = lean_ctor_get(v_e_4346_, 1);
lean_inc_ref(v_expr_4370_);
lean_dec_ref_known(v_e_4346_, 2);
v_e_4346_ = v_expr_4370_;
goto _start;
}
case 5:
{
lean_object* v_fn_4372_; 
v_fn_4372_ = lean_ctor_get(v_e_4346_, 0);
if (lean_obj_tag(v_fn_4372_) == 4)
{
lean_object* v_declName_4373_; 
v_declName_4373_ = lean_ctor_get(v_fn_4372_, 0);
lean_inc(v_declName_4373_);
if (lean_obj_tag(v_declName_4373_) == 1)
{
lean_object* v_pre_4374_; 
v_pre_4374_ = lean_ctor_get(v_declName_4373_, 0);
if (lean_obj_tag(v_pre_4374_) == 0)
{
lean_object* v_arg_4375_; lean_object* v_str_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; 
v_arg_4375_ = lean_ctor_get(v_e_4346_, 1);
lean_inc_ref(v_arg_4375_);
lean_dec_ref_known(v_e_4346_, 2);
v_str_4376_ = lean_ctor_get(v_declName_4373_, 1);
lean_inc_ref(v_str_4376_);
lean_dec_ref_known(v_declName_4373_, 2);
v___x_4377_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4378_ = lean_string_dec_eq(v_str_4376_, v___x_4377_);
lean_dec_ref(v_str_4376_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
lean_dec_ref(v_arg_4375_);
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4379_ = lean_box(2);
return v___x_4379_;
}
else
{
v_e_4346_ = v_arg_4375_;
goto _start;
}
}
else
{
lean_object* v___x_4381_; 
lean_dec_ref_known(v_declName_4373_, 2);
lean_dec_ref_known(v_e_4346_, 2);
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4381_ = lean_box(2);
return v___x_4381_;
}
}
else
{
lean_object* v___x_4382_; 
lean_dec(v_declName_4373_);
lean_dec_ref_known(v_e_4346_, 2);
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4382_ = lean_box(2);
return v___x_4382_;
}
}
else
{
lean_object* v___x_4383_; 
lean_dec_ref_known(v_e_4346_, 2);
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4383_ = lean_box(2);
return v___x_4383_;
}
}
default: 
{
lean_object* v___x_4384_; 
lean_dec(v_numArgs_4347_);
lean_dec_ref(v_e_4346_);
lean_dec_ref(v_00_u03c3_4345_);
v___x_4384_ = lean_box(2);
return v___x_4384_;
}
}
v___jp_4348_:
{
uint8_t v___x_4350_; 
v___x_4350_ = l_Lean_Level_isNeverZero(v___y_4349_);
if (v___x_4350_ == 0)
{
uint8_t v___x_4351_; 
v___x_4351_ = l_Lean_Level_isZero(v___y_4349_);
lean_dec(v___y_4349_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_box(2);
return v___x_4352_;
}
else
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_box(1);
return v___x_4353_;
}
}
else
{
lean_object* v___x_4354_; 
lean_dec(v___y_4349_);
v___x_4354_ = lean_box(0);
return v___x_4354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_00_u03c3_4385_, lean_object* v_r_4386_, lean_object* v_binderType_4387_){
_start:
{
if (lean_obj_tag(v_r_4386_) == 3)
{
lean_object* v_idx_4388_; lean_object* v_numArgs_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4401_; 
v_idx_4388_ = lean_ctor_get(v_r_4386_, 0);
v_numArgs_4389_ = lean_ctor_get(v_r_4386_, 1);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_r_4386_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4391_ = v_r_4386_;
v_isShared_4392_ = v_isSharedCheck_4401_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_numArgs_4389_);
lean_inc(v_idx_4388_);
lean_dec(v_r_4386_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4401_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v_zero_4393_; uint8_t v_isZero_4394_; 
v_zero_4393_ = lean_unsigned_to_nat(0u);
v_isZero_4394_ = lean_nat_dec_eq(v_idx_4388_, v_zero_4393_);
if (v_isZero_4394_ == 1)
{
lean_object* v___x_4395_; 
lean_del_object(v___x_4391_);
lean_dec(v_idx_4388_);
v___x_4395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_00_u03c3_4385_, v_binderType_4387_, v_numArgs_4389_);
return v___x_4395_;
}
else
{
lean_object* v_one_4396_; lean_object* v_n_4397_; lean_object* v___x_4399_; 
lean_dec_ref(v_binderType_4387_);
lean_dec_ref(v_00_u03c3_4385_);
v_one_4396_ = lean_unsigned_to_nat(1u);
v_n_4397_ = lean_nat_sub(v_idx_4388_, v_one_4396_);
lean_dec(v_idx_4388_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v_n_4397_);
v___x_4399_ = v___x_4391_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_n_4397_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_numArgs_4389_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_4387_);
lean_dec_ref(v_00_u03c3_4385_);
return v_r_4386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_00_u03c3_4402_, lean_object* v_x_4403_, lean_object* v_x_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_type_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; 
switch(lean_obj_tag(v_x_4403_))
{
case 7:
{
lean_object* v_binderType_4443_; lean_object* v_body_4444_; lean_object* v_zero_4445_; uint8_t v_isZero_4446_; 
v_binderType_4443_ = lean_ctor_get(v_x_4403_, 1);
v_body_4444_ = lean_ctor_get(v_x_4403_, 2);
v_zero_4445_ = lean_unsigned_to_nat(0u);
v_isZero_4446_ = lean_nat_dec_eq(v_x_4404_, v_zero_4445_);
if (v_isZero_4446_ == 1)
{
v_type_4411_ = v_x_4403_;
v___y_4412_ = v_a_4405_;
v___y_4413_ = v_a_4406_;
v___y_4414_ = v_a_4407_;
v___y_4415_ = v_a_4408_;
goto v___jp_4410_;
}
else
{
lean_object* v_one_4447_; lean_object* v_n_4448_; lean_object* v___x_4449_; 
lean_inc_ref(v_body_4444_);
lean_inc_ref(v_binderType_4443_);
lean_dec_ref_known(v_x_4403_, 3);
v_one_4447_ = lean_unsigned_to_nat(1u);
v_n_4448_ = lean_nat_sub(v_x_4404_, v_one_4447_);
lean_inc_ref(v_00_u03c3_4402_);
v___x_4449_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4402_, v_body_4444_, v_n_4448_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
lean_dec(v_n_4448_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4458_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4452_ = v___x_4449_;
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4449_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4458_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4402_, v_a_4450_, v_binderType_4443_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 0, v___x_4454_);
v___x_4456_ = v___x_4452_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
else
{
lean_dec_ref(v_binderType_4443_);
lean_dec_ref(v_00_u03c3_4402_);
return v___x_4449_;
}
}
}
case 8:
{
lean_object* v_type_4459_; lean_object* v_body_4460_; lean_object* v___x_4461_; 
v_type_4459_ = lean_ctor_get(v_x_4403_, 1);
lean_inc_ref(v_type_4459_);
v_body_4460_ = lean_ctor_get(v_x_4403_, 3);
lean_inc_ref(v_body_4460_);
lean_dec_ref_known(v_x_4403_, 4);
lean_inc_ref(v_00_u03c3_4402_);
v___x_4461_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4402_, v_body_4460_, v_x_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4470_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4464_ = v___x_4461_;
v_isShared_4465_ = v_isSharedCheck_4470_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4461_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4470_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4466_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4402_, v_a_4462_, v_type_4459_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4466_);
v___x_4468_ = v___x_4464_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
else
{
lean_dec_ref(v_type_4459_);
lean_dec_ref(v_00_u03c3_4402_);
return v___x_4461_;
}
}
case 10:
{
lean_object* v_expr_4471_; 
v_expr_4471_ = lean_ctor_get(v_x_4403_, 1);
lean_inc_ref(v_expr_4471_);
lean_dec_ref_known(v_x_4403_, 2);
v_x_4403_ = v_expr_4471_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; 
lean_dec_ref(v_00_u03c3_4402_);
v_deBruijnIndex_4473_ = lean_ctor_get(v_x_4403_, 0);
lean_inc(v_deBruijnIndex_4473_);
lean_dec_ref_known(v_x_4403_, 1);
v___x_4474_ = lean_unsigned_to_nat(0u);
v___x_4475_ = lean_nat_dec_eq(v_x_4404_, v___x_4474_);
if (v___x_4475_ == 0)
{
lean_dec(v_deBruijnIndex_4473_);
goto v___jp_4440_;
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4476_, 0, v_deBruijnIndex_4473_);
lean_ctor_set(v___x_4476_, 1, v___x_4474_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
default: 
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = lean_unsigned_to_nat(0u);
v___x_4479_ = lean_nat_dec_eq(v_x_4404_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_dec_ref(v_x_4403_);
lean_dec_ref(v_00_u03c3_4402_);
goto v___jp_4440_;
}
else
{
v_type_4411_ = v_x_4403_;
v___y_4412_ = v_a_4405_;
v___y_4413_ = v_a_4406_;
v___y_4414_ = v_a_4407_;
v___y_4415_ = v_a_4408_;
goto v___jp_4410_;
}
}
}
v___jp_4410_:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_Expr_getAppFn(v_type_4411_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_deBruijnIndex_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
lean_dec_ref(v_00_u03c3_4402_);
v_deBruijnIndex_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_deBruijnIndex_4417_);
lean_dec_ref_known(v___x_4416_, 1);
v___x_4418_ = l_Lean_Expr_getAppNumArgs(v_type_4411_);
lean_dec_ref(v_type_4411_);
v___x_4419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4419_, 0, v_deBruijnIndex_4417_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
return v___x_4420_;
}
else
{
lean_object* v___x_4421_; 
lean_dec_ref(v___x_4416_);
v___x_4421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4402_, v_type_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4431_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4431_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4431_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
uint8_t v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; 
v___x_4426_ = lean_unbox(v_a_4422_);
lean_dec(v_a_4422_);
v___x_4427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4426_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4427_);
v___x_4429_ = v___x_4424_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
v_a_4432_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4421_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4421_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
v___jp_4440_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = lean_box(2);
v___x_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
return v___x_4442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_00_u03c3_4480_, lean_object* v_x_4481_, lean_object* v_x_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4480_, v_x_4481_, v_x_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_x_4482_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_00_u03c3_4489_, lean_object* v_e_4490_, lean_object* v_n_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4489_, v_e_4490_, v_n_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4507_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4500_ = v___x_4497_;
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4497_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
uint8_t v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4502_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4498_);
lean_dec(v_a_4498_);
v___x_4503_ = lean_box(v___x_4502_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4503_);
v___x_4505_ = v___x_4500_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_a_4508_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4497_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4497_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_00_u03c3_4516_, lean_object* v_e_4517_, lean_object* v_n_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_00_u03c3_4516_, v_e_4517_, v_n_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_n_4518_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
switch(lean_obj_tag(v_x_4525_))
{
case 1:
{
lean_object* v_fvarId_4531_; lean_object* v___x_4532_; 
v_fvarId_4531_ = lean_ctor_get(v_x_4525_, 0);
lean_inc(v_fvarId_4531_);
lean_dec_ref_known(v_x_4525_, 1);
v___x_4532_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4531_, v_a_4526_, v_a_4528_, v_a_4529_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4535_ = lean_unsigned_to_nat(0u);
v___x_4536_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4534_, v_a_4533_, v___x_4535_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4536_;
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_a_4537_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4532_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4532_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4545_; lean_object* v___x_4546_; 
v_mvarId_4545_ = lean_ctor_get(v_x_4525_, 0);
lean_inc(v_mvarId_4545_);
lean_dec_ref_known(v_x_4525_, 1);
v___x_4546_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4545_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4546_, 1);
v___x_4548_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4549_ = lean_unsigned_to_nat(0u);
v___x_4550_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4548_, v_a_4547_, v___x_4549_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4550_;
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_a_4551_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4546_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4546_);
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
case 3:
{
uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_dec_ref_known(v_x_4525_, 1);
v___x_4559_ = 0;
v___x_4560_ = lean_box(v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
case 4:
{
lean_object* v_declName_4562_; lean_object* v_us_4563_; lean_object* v___x_4564_; 
v_declName_4562_ = lean_ctor_get(v_x_4525_, 0);
lean_inc(v_declName_4562_);
v_us_4563_ = lean_ctor_get(v_x_4525_, 1);
lean_inc(v_us_4563_);
lean_dec_ref_known(v_x_4525_, 2);
v___x_4564_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4562_, v_us_4563_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v_fst_4566_; lean_object* v_snd_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4564_, 1);
v_fst_4566_ = lean_ctor_get(v_a_4565_, 0);
lean_inc(v_fst_4566_);
v_snd_4567_ = lean_ctor_get(v_a_4565_, 1);
lean_inc(v_snd_4567_);
lean_dec(v_a_4565_);
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4567_, v_fst_4566_, v___x_4568_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4569_;
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
v_a_4570_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4564_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4564_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
case 5:
{
lean_object* v_fn_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_fn_4578_ = lean_ctor_get(v_x_4525_, 0);
lean_inc_ref(v_fn_4578_);
lean_dec_ref_known(v_x_4525_, 2);
v___x_4579_ = lean_unsigned_to_nat(1u);
v___x_4580_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4578_, v___x_4579_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4580_;
}
case 6:
{
lean_object* v_body_4581_; 
v_body_4581_ = lean_ctor_get(v_x_4525_, 2);
lean_inc_ref(v_body_4581_);
lean_dec_ref_known(v_x_4525_, 3);
v_x_4525_ = v_body_4581_;
goto _start;
}
case 7:
{
uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
lean_dec_ref_known(v_x_4525_, 3);
v___x_4583_ = 0;
v___x_4584_ = lean_box(v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
case 8:
{
lean_object* v_body_4586_; 
v_body_4586_ = lean_ctor_get(v_x_4525_, 3);
lean_inc_ref(v_body_4586_);
lean_dec_ref_known(v_x_4525_, 4);
v_x_4525_ = v_body_4586_;
goto _start;
}
case 9:
{
uint8_t v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
lean_dec_ref_known(v_x_4525_, 1);
v___x_4588_ = 0;
v___x_4589_ = lean_box(v___x_4588_);
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
return v___x_4590_;
}
case 10:
{
lean_object* v_expr_4591_; 
v_expr_4591_ = lean_ctor_get(v_x_4525_, 1);
lean_inc_ref(v_expr_4591_);
lean_dec_ref_known(v_x_4525_, 2);
v_x_4525_ = v_expr_4591_;
goto _start;
}
default: 
{
uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_dec_ref(v_x_4525_);
v___x_4593_ = 2;
v___x_4594_ = lean_box(v___x_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4596_, lean_object* v_x_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
switch(lean_obj_tag(v_x_4596_))
{
case 4:
{
lean_object* v_declName_4603_; lean_object* v_us_4604_; lean_object* v___x_4605_; 
v_declName_4603_ = lean_ctor_get(v_x_4596_, 0);
lean_inc(v_declName_4603_);
v_us_4604_ = lean_ctor_get(v_x_4596_, 1);
lean_inc(v_us_4604_);
lean_dec_ref_known(v_x_4596_, 2);
v___x_4605_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4603_, v_us_4604_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v_fst_4607_; lean_object* v_snd_4608_; lean_object* v___x_4609_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v_fst_4607_ = lean_ctor_get(v_a_4606_, 0);
lean_inc(v_fst_4607_);
v_snd_4608_ = lean_ctor_get(v_a_4606_, 1);
lean_inc(v_snd_4608_);
lean_dec(v_a_4606_);
v___x_4609_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4608_, v_fst_4607_, v_x_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_x_4597_);
return v___x_4609_;
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec(v_x_4597_);
v_a_4610_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4605_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4605_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4618_; lean_object* v___x_4619_; 
v_fvarId_4618_ = lean_ctor_get(v_x_4596_, 0);
lean_inc(v_fvarId_4618_);
lean_dec_ref_known(v_x_4596_, 1);
v___x_4619_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4618_, v_a_4598_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref_known(v___x_4619_, 1);
v___x_4621_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4622_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4621_, v_a_4620_, v_x_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_x_4597_);
return v___x_4622_;
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec(v_x_4597_);
v_a_4623_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4619_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4619_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4631_; lean_object* v___x_4632_; 
v_mvarId_4631_ = lean_ctor_get(v_x_4596_, 0);
lean_inc(v_mvarId_4631_);
lean_dec_ref_known(v_x_4596_, 1);
v___x_4632_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4631_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v___x_4634_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4635_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4634_, v_a_4633_, v_x_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_x_4597_);
return v___x_4635_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_x_4597_);
v_a_4636_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4632_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4632_);
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
case 5:
{
lean_object* v_fn_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v_fn_4644_ = lean_ctor_get(v_x_4596_, 0);
lean_inc_ref(v_fn_4644_);
lean_dec_ref_known(v_x_4596_, 2);
v___x_4645_ = lean_unsigned_to_nat(1u);
v___x_4646_ = lean_nat_add(v_x_4597_, v___x_4645_);
lean_dec(v_x_4597_);
v_x_4596_ = v_fn_4644_;
v_x_4597_ = v___x_4646_;
goto _start;
}
case 10:
{
lean_object* v_expr_4648_; 
v_expr_4648_ = lean_ctor_get(v_x_4596_, 1);
lean_inc_ref(v_expr_4648_);
lean_dec_ref_known(v_x_4596_, 2);
v_x_4596_ = v_expr_4648_;
goto _start;
}
case 8:
{
lean_object* v_body_4650_; 
v_body_4650_ = lean_ctor_get(v_x_4596_, 3);
lean_inc_ref(v_body_4650_);
lean_dec_ref_known(v_x_4596_, 4);
v_x_4596_ = v_body_4650_;
goto _start;
}
case 6:
{
lean_object* v_body_4652_; lean_object* v_zero_4653_; uint8_t v_isZero_4654_; 
v_body_4652_ = lean_ctor_get(v_x_4596_, 2);
lean_inc_ref(v_body_4652_);
lean_dec_ref_known(v_x_4596_, 3);
v_zero_4653_ = lean_unsigned_to_nat(0u);
v_isZero_4654_ = lean_nat_dec_eq(v_x_4597_, v_zero_4653_);
if (v_isZero_4654_ == 1)
{
lean_object* v___x_4655_; 
lean_dec(v_x_4597_);
v___x_4655_ = l_Lean_Meta_isProofQuick(v_body_4652_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
return v___x_4655_;
}
else
{
lean_object* v_one_4656_; lean_object* v_n_4657_; 
v_one_4656_ = lean_unsigned_to_nat(1u);
v_n_4657_ = lean_nat_sub(v_x_4597_, v_one_4656_);
lean_dec(v_x_4597_);
v_x_4596_ = v_body_4652_;
v_x_4597_ = v_n_4657_;
goto _start;
}
}
default: 
{
uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_dec(v_x_4597_);
lean_dec_ref(v_x_4596_);
v___x_4659_ = 2;
v___x_4660_ = lean_box(v___x_4659_);
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
return v___x_4661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4662_, lean_object* v_x_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4662_, v_x_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_Meta_isProofQuick(v_x_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v___x_4683_; 
lean_inc_ref(v_e_4677_);
v___x_4683_ = l_Lean_Meta_isProofQuick(v_e_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4710_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4686_ = v___x_4683_;
v_isShared_4687_ = v_isSharedCheck_4710_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4710_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
uint8_t v___x_4688_; 
v___x_4688_ = lean_unbox(v_a_4684_);
lean_dec(v_a_4684_);
switch(v___x_4688_)
{
case 0:
{
uint8_t v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4692_; 
lean_dec_ref(v_e_4677_);
v___x_4689_ = 0;
v___x_4690_ = lean_box(v___x_4689_);
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v___x_4690_);
v___x_4692_ = v___x_4686_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
case 1:
{
uint8_t v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
lean_dec_ref(v_e_4677_);
v___x_4694_ = 1;
v___x_4695_ = lean_box(v___x_4694_);
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v___x_4695_);
v___x_4697_ = v___x_4686_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
default: 
{
lean_object* v___x_4699_; 
lean_del_object(v___x_4686_);
lean_inc(v_a_4681_);
lean_inc_ref(v_a_4680_);
lean_inc(v_a_4679_);
lean_inc_ref(v_a_4678_);
v___x_4699_ = lean_infer_type(v_e_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4701_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4699_, 1);
v___x_4701_ = l_Lean_Meta_isProp(v_a_4700_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
return v___x_4701_;
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
v_a_4702_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4699_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4699_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec_ref(v_e_4677_);
v_a_4711_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4683_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4683_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_Lean_Meta_isProof(v_e_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4726_, lean_object* v_x_4727_){
_start:
{
switch(lean_obj_tag(v_x_4726_))
{
case 3:
{
lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4733_ = lean_unsigned_to_nat(0u);
v___x_4734_ = lean_nat_dec_eq(v_x_4727_, v___x_4733_);
lean_dec(v_x_4727_);
if (v___x_4734_ == 0)
{
goto v___jp_4729_;
}
else
{
uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = 1;
v___x_4736_ = lean_box(v___x_4735_);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
}
case 7:
{
lean_object* v_body_4738_; lean_object* v_zero_4739_; uint8_t v_isZero_4740_; 
v_body_4738_ = lean_ctor_get(v_x_4726_, 2);
v_zero_4739_ = lean_unsigned_to_nat(0u);
v_isZero_4740_ = lean_nat_dec_eq(v_x_4727_, v_zero_4739_);
if (v_isZero_4740_ == 1)
{
uint8_t v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_dec(v_x_4727_);
v___x_4741_ = 0;
v___x_4742_ = lean_box(v___x_4741_);
v___x_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
return v___x_4743_;
}
else
{
lean_object* v_one_4744_; lean_object* v_n_4745_; 
v_one_4744_ = lean_unsigned_to_nat(1u);
v_n_4745_ = lean_nat_sub(v_x_4727_, v_one_4744_);
lean_dec(v_x_4727_);
v_x_4726_ = v_body_4738_;
v_x_4727_ = v_n_4745_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4747_; 
v_body_4747_ = lean_ctor_get(v_x_4726_, 3);
v_x_4726_ = v_body_4747_;
goto _start;
}
case 10:
{
lean_object* v_expr_4749_; 
v_expr_4749_ = lean_ctor_get(v_x_4726_, 1);
v_x_4726_ = v_expr_4749_;
goto _start;
}
default: 
{
lean_dec(v_x_4727_);
goto v___jp_4729_;
}
}
v___jp_4729_:
{
uint8_t v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4730_ = 2;
v___x_4731_ = lean_box(v___x_4730_);
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
return v___x_4732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4751_, lean_object* v_x_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4751_, v_x_4752_);
lean_dec_ref(v_x_4751_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4755_, lean_object* v_x_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4755_, v_x_4756_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4763_, lean_object* v_x_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4763_, v_x_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec_ref(v_x_4763_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4771_, lean_object* v_x_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
switch(lean_obj_tag(v_x_4771_))
{
case 4:
{
lean_object* v_declName_4778_; lean_object* v_us_4779_; lean_object* v___x_4780_; 
v_declName_4778_ = lean_ctor_get(v_x_4771_, 0);
lean_inc(v_declName_4778_);
v_us_4779_ = lean_ctor_get(v_x_4771_, 1);
lean_inc(v_us_4779_);
lean_dec_ref_known(v_x_4771_, 2);
v___x_4780_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4778_, v_us_4779_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v_fst_4782_; lean_object* v___x_4783_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4780_, 1);
v_fst_4782_ = lean_ctor_get(v_a_4781_, 0);
lean_inc(v_fst_4782_);
lean_dec(v_a_4781_);
v___x_4783_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_4782_, v_x_4772_);
lean_dec(v_fst_4782_);
return v___x_4783_;
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec(v_x_4772_);
v_a_4784_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4780_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4780_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4792_; lean_object* v___x_4793_; 
v_fvarId_4792_ = lean_ctor_get(v_x_4771_, 0);
lean_inc(v_fvarId_4792_);
lean_dec_ref_known(v_x_4771_, 1);
v___x_4793_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4792_, v_a_4773_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4795_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v___x_4795_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4794_, v_x_4772_);
lean_dec(v_a_4794_);
return v___x_4795_;
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
lean_dec(v_x_4772_);
v_a_4796_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4793_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4793_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4804_; lean_object* v___x_4805_; 
v_mvarId_4804_ = lean_ctor_get(v_x_4771_, 0);
lean_inc(v_mvarId_4804_);
lean_dec_ref_known(v_x_4771_, 1);
v___x_4805_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4804_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4807_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4805_, 1);
v___x_4807_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4806_, v_x_4772_);
lean_dec(v_a_4806_);
return v___x_4807_;
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_x_4772_);
v_a_4808_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4805_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4805_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
case 5:
{
lean_object* v_fn_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v_fn_4816_ = lean_ctor_get(v_x_4771_, 0);
lean_inc_ref(v_fn_4816_);
lean_dec_ref_known(v_x_4771_, 2);
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = lean_nat_add(v_x_4772_, v___x_4817_);
lean_dec(v_x_4772_);
v_x_4771_ = v_fn_4816_;
v_x_4772_ = v___x_4818_;
goto _start;
}
case 10:
{
lean_object* v_expr_4820_; 
v_expr_4820_ = lean_ctor_get(v_x_4771_, 1);
lean_inc_ref(v_expr_4820_);
lean_dec_ref_known(v_x_4771_, 2);
v_x_4771_ = v_expr_4820_;
goto _start;
}
case 8:
{
lean_object* v_body_4822_; 
v_body_4822_ = lean_ctor_get(v_x_4771_, 3);
lean_inc_ref(v_body_4822_);
lean_dec_ref_known(v_x_4771_, 4);
v_x_4771_ = v_body_4822_;
goto _start;
}
case 6:
{
lean_object* v_body_4824_; lean_object* v_zero_4825_; uint8_t v_isZero_4826_; 
v_body_4824_ = lean_ctor_get(v_x_4771_, 2);
lean_inc_ref(v_body_4824_);
lean_dec_ref_known(v_x_4771_, 3);
v_zero_4825_ = lean_unsigned_to_nat(0u);
v_isZero_4826_ = lean_nat_dec_eq(v_x_4772_, v_zero_4825_);
if (v_isZero_4826_ == 1)
{
uint8_t v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_dec_ref(v_body_4824_);
lean_dec(v_x_4772_);
v___x_4827_ = 0;
v___x_4828_ = lean_box(v___x_4827_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
else
{
lean_object* v_one_4830_; lean_object* v_n_4831_; 
v_one_4830_ = lean_unsigned_to_nat(1u);
v_n_4831_ = lean_nat_sub(v_x_4772_, v_one_4830_);
lean_dec(v_x_4772_);
v_x_4771_ = v_body_4824_;
v_x_4772_ = v_n_4831_;
goto _start;
}
}
default: 
{
uint8_t v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec(v_x_4772_);
lean_dec_ref(v_x_4771_);
v___x_4833_ = 2;
v___x_4834_ = lean_box(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
return v___x_4835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4836_, lean_object* v_x_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4836_, v_x_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
switch(lean_obj_tag(v_x_4844_))
{
case 1:
{
lean_object* v_fvarId_4850_; lean_object* v___x_4851_; 
v_fvarId_4850_ = lean_ctor_get(v_x_4844_, 0);
lean_inc(v_fvarId_4850_);
lean_dec_ref_known(v_x_4844_, 1);
v___x_4851_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4850_, v_a_4845_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v___x_4853_ = lean_unsigned_to_nat(0u);
v___x_4854_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4852_, v___x_4853_);
lean_dec(v_a_4852_);
return v___x_4854_;
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
v_a_4855_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4851_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4851_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4863_; lean_object* v___x_4864_; 
v_mvarId_4863_ = lean_ctor_get(v_x_4844_, 0);
lean_inc(v_mvarId_4863_);
lean_dec_ref_known(v_x_4844_, 1);
v___x_4864_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4863_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = lean_unsigned_to_nat(0u);
v___x_4867_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4865_, v___x_4866_);
lean_dec(v_a_4865_);
return v___x_4867_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4864_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4864_);
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
case 3:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_dec_ref_known(v_x_4844_, 1);
v___x_4876_ = 1;
v___x_4877_ = lean_box(v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
case 4:
{
lean_object* v_declName_4879_; lean_object* v_us_4880_; lean_object* v___x_4881_; 
v_declName_4879_ = lean_ctor_get(v_x_4844_, 0);
lean_inc(v_declName_4879_);
v_us_4880_ = lean_ctor_get(v_x_4844_, 1);
lean_inc(v_us_4880_);
lean_dec_ref_known(v_x_4844_, 2);
v___x_4881_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4879_, v_us_4880_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v_fst_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
v_fst_4883_ = lean_ctor_get(v_a_4882_, 0);
lean_inc(v_fst_4883_);
lean_dec(v_a_4882_);
v___x_4884_ = lean_unsigned_to_nat(0u);
v___x_4885_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_4883_, v___x_4884_);
lean_dec(v_fst_4883_);
return v___x_4885_;
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_a_4886_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4881_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4881_);
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
case 5:
{
lean_object* v_fn_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v_fn_4894_ = lean_ctor_get(v_x_4844_, 0);
lean_inc_ref(v_fn_4894_);
lean_dec_ref_known(v_x_4844_, 2);
v___x_4895_ = lean_unsigned_to_nat(1u);
v___x_4896_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4894_, v___x_4895_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
return v___x_4896_;
}
case 6:
{
uint8_t v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_dec_ref_known(v_x_4844_, 3);
v___x_4897_ = 0;
v___x_4898_ = lean_box(v___x_4897_);
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
return v___x_4899_;
}
case 7:
{
uint8_t v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
lean_dec_ref_known(v_x_4844_, 3);
v___x_4900_ = 1;
v___x_4901_ = lean_box(v___x_4900_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
return v___x_4902_;
}
case 8:
{
lean_object* v_body_4903_; 
v_body_4903_ = lean_ctor_get(v_x_4844_, 3);
lean_inc_ref(v_body_4903_);
lean_dec_ref_known(v_x_4844_, 4);
v_x_4844_ = v_body_4903_;
goto _start;
}
case 9:
{
uint8_t v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_dec_ref_known(v_x_4844_, 1);
v___x_4905_ = 0;
v___x_4906_ = lean_box(v___x_4905_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
case 10:
{
lean_object* v_expr_4908_; 
v_expr_4908_ = lean_ctor_get(v_x_4844_, 1);
lean_inc_ref(v_expr_4908_);
lean_dec_ref_known(v_x_4844_, 2);
v_x_4844_ = v_expr_4908_;
goto _start;
}
default: 
{
uint8_t v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_dec_ref(v_x_4844_);
v___x_4910_ = 2;
v___x_4911_ = lean_box(v___x_4910_);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
return v___x_4912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Meta_isTypeQuick(v_x_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
lean_dec(v_a_4915_);
lean_dec_ref(v_a_4914_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v___x_4926_; 
lean_inc_ref(v_e_4920_);
v___x_4926_ = l_Lean_Meta_isTypeQuick(v_e_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4976_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4976_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4976_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
uint8_t v___x_4931_; 
v___x_4931_ = lean_unbox(v_a_4927_);
lean_dec(v_a_4927_);
switch(v___x_4931_)
{
case 0:
{
uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
lean_dec_ref(v_e_4920_);
v___x_4932_ = 0;
v___x_4933_ = lean_box(v___x_4932_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4933_);
v___x_4935_ = v___x_4929_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
case 1:
{
uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
lean_dec_ref(v_e_4920_);
v___x_4937_ = 1;
v___x_4938_ = lean_box(v___x_4937_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4938_);
v___x_4940_ = v___x_4929_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
default: 
{
lean_object* v___x_4942_; 
lean_del_object(v___x_4929_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
v___x_4942_ = lean_infer_type(v_e_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___x_4942_, 1);
v___x_4944_ = l_Lean_Meta_whnfD(v_a_4943_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4959_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4947_ = v___x_4944_;
v_isShared_4948_ = v_isSharedCheck_4959_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4944_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4959_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
if (lean_obj_tag(v_a_4945_) == 3)
{
uint8_t v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4952_; 
lean_dec_ref_known(v_a_4945_, 1);
v___x_4949_ = 1;
v___x_4950_ = lean_box(v___x_4949_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4950_);
v___x_4952_ = v___x_4947_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4950_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
else
{
uint8_t v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4957_; 
lean_dec(v_a_4945_);
v___x_4954_ = 0;
v___x_4955_ = lean_box(v___x_4954_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4955_);
v___x_4957_ = v___x_4947_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v___x_4955_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
v_a_4960_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4944_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4944_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
v_a_4968_ = lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4942_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4942_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec_ref(v_e_4920_);
v_a_4977_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4926_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4926_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_Meta_isType(v_e_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4992_){
_start:
{
switch(lean_obj_tag(v_x_4992_))
{
case 7:
{
lean_object* v_body_4993_; 
v_body_4993_ = lean_ctor_get(v_x_4992_, 2);
v_x_4992_ = v_body_4993_;
goto _start;
}
case 3:
{
lean_object* v_u_4995_; lean_object* v___x_4996_; 
v_u_4995_ = lean_ctor_get(v_x_4992_, 0);
lean_inc(v_u_4995_);
v___x_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4996_, 0, v_u_4995_);
return v___x_4996_;
}
default: 
{
lean_object* v___x_4997_; 
v___x_4997_ = lean_box(0);
return v___x_4997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4998_);
lean_dec_ref(v_x_4998_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5000_, lean_object* v_body_5001_, lean_object* v_x_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5000_, v_body_5001_, v_x_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5011_, lean_object* v_xs_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_l_5019_; 
switch(lean_obj_tag(v_type_5011_))
{
case 3:
{
lean_object* v_u_5022_; 
lean_dec_ref(v_xs_5012_);
v_u_5022_ = lean_ctor_get(v_type_5011_, 0);
lean_inc(v_u_5022_);
lean_dec_ref_known(v_type_5011_, 1);
v_l_5019_ = v_u_5022_;
goto v___jp_5018_;
}
case 7:
{
lean_object* v_binderName_5023_; lean_object* v_binderType_5024_; lean_object* v_body_5025_; uint8_t v_binderInfo_5026_; lean_object* v___f_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_binderName_5023_ = lean_ctor_get(v_type_5011_, 0);
lean_inc(v_binderName_5023_);
v_binderType_5024_ = lean_ctor_get(v_type_5011_, 1);
lean_inc_ref(v_binderType_5024_);
v_body_5025_ = lean_ctor_get(v_type_5011_, 2);
lean_inc_ref(v_body_5025_);
v_binderInfo_5026_ = lean_ctor_get_uint8(v_type_5011_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5011_, 3);
lean_inc_ref(v_xs_5012_);
v___f_5027_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5027_, 0, v_xs_5012_);
lean_closure_set(v___f_5027_, 1, v_body_5025_);
v___x_5028_ = lean_expr_instantiate_rev(v_binderType_5024_, v_xs_5012_);
lean_dec_ref(v_xs_5012_);
lean_dec_ref(v_binderType_5024_);
v___x_5029_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5023_, v_binderInfo_5026_, v___x_5028_, v___f_5027_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
return v___x_5029_;
}
default: 
{
lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5030_ = lean_expr_instantiate_rev(v_type_5011_, v_xs_5012_);
lean_dec_ref(v_xs_5012_);
lean_dec_ref(v_type_5011_);
v___x_5031_ = l_Lean_Meta_whnfD(v___x_5030_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5043_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5043_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5043_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
switch(lean_obj_tag(v_a_5032_))
{
case 3:
{
lean_object* v_u_5036_; 
lean_del_object(v___x_5034_);
v_u_5036_ = lean_ctor_get(v_a_5032_, 0);
lean_inc(v_u_5036_);
lean_dec_ref_known(v_a_5032_, 1);
v_l_5019_ = v_u_5036_;
goto v___jp_5018_;
}
case 7:
{
lean_object* v___x_5037_; 
lean_del_object(v___x_5034_);
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5011_ = v_a_5032_;
v_xs_5012_ = v___x_5037_;
goto _start;
}
default: 
{
lean_object* v___x_5039_; lean_object* v___x_5041_; 
lean_dec(v_a_5032_);
v___x_5039_ = lean_box(0);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5039_);
v___x_5041_ = v___x_5034_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5039_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5031_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5031_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
}
v___jp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5020_, 0, v_l_5019_);
v___x_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5020_);
return v___x_5021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5052_, lean_object* v_body_5053_, lean_object* v_x_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = lean_array_push(v_xs_5052_, v_x_5054_);
v___x_5061_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5053_, v___x_5060_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5062_, lean_object* v_xs_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5062_, v_xs_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5070_, lean_object* v_cache_5071_, lean_object* v_a_x3f_5072_){
_start:
{
lean_object* v___x_5074_; lean_object* v_mctx_5075_; lean_object* v_zetaDeltaFVarIds_5076_; lean_object* v_postponed_5077_; lean_object* v_diag_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5088_; 
v___x_5074_ = lean_st_ref_take(v_a_5070_);
v_mctx_5075_ = lean_ctor_get(v___x_5074_, 0);
v_zetaDeltaFVarIds_5076_ = lean_ctor_get(v___x_5074_, 2);
v_postponed_5077_ = lean_ctor_get(v___x_5074_, 3);
v_diag_5078_ = lean_ctor_get(v___x_5074_, 4);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v___x_5074_, 1);
lean_dec(v_unused_5089_);
v___x_5080_ = v___x_5074_;
v_isShared_5081_ = v_isSharedCheck_5088_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_diag_5078_);
lean_inc(v_postponed_5077_);
lean_inc(v_zetaDeltaFVarIds_5076_);
lean_inc(v_mctx_5075_);
lean_dec(v___x_5074_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5088_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5082_; lean_object* v___x_5084_; 
v___x_5082_ = lean_box(0);
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 1, v_cache_5071_);
v___x_5084_ = v___x_5080_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_mctx_5075_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v_cache_5071_);
lean_ctor_set(v_reuseFailAlloc_5087_, 2, v_zetaDeltaFVarIds_5076_);
lean_ctor_set(v_reuseFailAlloc_5087_, 3, v_postponed_5077_);
lean_ctor_set(v_reuseFailAlloc_5087_, 4, v_diag_5078_);
v___x_5084_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_st_ref_put(v_a_5070_, v___x_5084_);
v___x_5086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5082_);
return v___x_5086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5090_, lean_object* v_cache_5091_, lean_object* v_a_x3f_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5090_, v_cache_5091_, v_a_x3f_5092_);
lean_dec(v_a_x3f_5092_);
lean_dec(v_a_5090_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5095_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v_cache_5104_; lean_object* v___x_5105_; 
v___x_5102_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5103_ = lean_st_ref_get(v_a_5097_);
v_cache_5104_ = lean_ctor_get(v___x_5103_, 1);
lean_inc_ref(v_cache_5104_);
lean_dec(v___x_5103_);
v___x_5105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5095_, v___x_5102_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5122_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5122_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5122_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
lean_inc(v_a_5106_);
if (v_isShared_5109_ == 0)
{
lean_ctor_set_tag(v___x_5108_, 1);
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
lean_object* v___x_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
v___x_5112_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5097_, v_cache_5104_, v___x_5111_);
lean_dec_ref(v___x_5111_);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; 
v_unused_5120_ = lean_ctor_get(v___x_5112_, 0);
lean_dec(v_unused_5120_);
v___x_5114_ = v___x_5112_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_dec(v___x_5112_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 0, v_a_5106_);
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5106_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
v_a_5123_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5105_, 1);
v___x_5124_ = lean_box(0);
v___x_5125_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5097_, v_cache_5104_, v___x_5124_);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5132_ == 0)
{
lean_object* v_unused_5133_; 
v_unused_5133_ = lean_ctor_get(v___x_5125_, 0);
lean_dec(v_unused_5133_);
v___x_5127_ = v___x_5125_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_dec(v___x_5125_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
lean_ctor_set_tag(v___x_5127_, 1);
lean_ctor_set(v___x_5127_, 0, v_a_5123_);
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5123_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
else
{
lean_object* v___x_5134_; 
lean_dec_ref(v_type_5095_);
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5101_);
return v___x_5134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5163_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5151_ = v___x_5148_;
v_isShared_5152_ = v_isSharedCheck_5163_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5148_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5163_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
if (lean_obj_tag(v_a_5149_) == 0)
{
uint8_t v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5156_; 
v___x_5153_ = 0;
v___x_5154_ = lean_box(v___x_5153_);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5154_);
v___x_5156_ = v___x_5151_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5154_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
else
{
uint8_t v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5161_; 
lean_dec_ref_known(v_a_5149_, 1);
v___x_5158_ = 1;
v___x_5159_ = lean_box(v___x_5158_);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5159_);
v___x_5161_ = v___x_5151_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
v_a_5164_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5148_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5148_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Meta_isTypeFormerType(v_type_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
return v_res_5178_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5179_, lean_object* v_x_5180_){
_start:
{
if (lean_obj_tag(v_x_5179_) == 0)
{
if (lean_obj_tag(v_x_5180_) == 0)
{
uint8_t v___x_5181_; 
v___x_5181_ = 1;
return v___x_5181_;
}
else
{
uint8_t v___x_5182_; 
v___x_5182_ = 0;
return v___x_5182_;
}
}
else
{
if (lean_obj_tag(v_x_5180_) == 0)
{
uint8_t v___x_5183_; 
v___x_5183_ = 0;
return v___x_5183_;
}
else
{
lean_object* v_val_5184_; lean_object* v_val_5185_; uint8_t v___x_5186_; 
v_val_5184_ = lean_ctor_get(v_x_5179_, 0);
v_val_5185_ = lean_ctor_get(v_x_5180_, 0);
v___x_5186_ = lean_level_eq(v_val_5184_, v_val_5185_);
return v___x_5186_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5187_, lean_object* v_x_5188_){
_start:
{
uint8_t v_res_5189_; lean_object* v_r_5190_; 
v_res_5189_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5187_, v_x_5188_);
lean_dec(v_x_5188_);
lean_dec(v_x_5187_);
v_r_5190_ = lean_box(v_res_5189_);
return v_r_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5210_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5210_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5210_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5204_; uint8_t v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5208_; 
v___x_5204_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5205_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5200_, v___x_5204_);
lean_dec(v_a_5200_);
v___x_5206_ = lean_box(v___x_5205_);
if (v_isShared_5203_ == 0)
{
lean_ctor_set(v___x_5202_, 0, v___x_5206_);
v___x_5208_ = v___x_5202_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5206_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
v_a_5211_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5199_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5199_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Lean_Meta_isPropFormerType(v_type_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v___x_5232_; 
lean_inc(v_a_5230_);
lean_inc_ref(v_a_5229_);
lean_inc(v_a_5228_);
lean_inc_ref(v_a_5227_);
v___x_5232_ = lean_infer_type(v_e_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5234_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref_known(v___x_5232_, 1);
v___x_5234_ = l_Lean_Meta_isTypeFormerType(v_a_5233_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
return v___x_5234_;
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
v_a_5235_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5232_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5232_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_Lean_Meta_isTypeFormer(v_e_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5250_, lean_object* v_maxFVars_x3f_5251_, lean_object* v_k_5252_, uint8_t v_cleanupAnnotations_5253_, uint8_t v_whnfType_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___f_5260_; lean_object* v___x_5261_; 
v___f_5260_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5260_, 0, v_k_5252_);
v___x_5261_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5250_, v_maxFVars_x3f_5251_, v___f_5260_, v_cleanupAnnotations_5253_, v_whnfType_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5261_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5261_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5277_; 
v_a_5270_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5272_ = v___x_5261_;
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5261_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5278_, lean_object* v_maxFVars_x3f_5279_, lean_object* v_k_5280_, lean_object* v_cleanupAnnotations_5281_, lean_object* v_whnfType_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5288_; uint8_t v_whnfType_boxed_5289_; lean_object* v_res_5290_; 
v_cleanupAnnotations_boxed_5288_ = lean_unbox(v_cleanupAnnotations_5281_);
v_whnfType_boxed_5289_ = lean_unbox(v_whnfType_5282_);
v_res_5290_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5278_, v_maxFVars_x3f_5279_, v_k_5280_, v_cleanupAnnotations_boxed_5288_, v_whnfType_boxed_5289_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5291_, lean_object* v_type_5292_, lean_object* v_maxFVars_x3f_5293_, lean_object* v_k_5294_, uint8_t v_cleanupAnnotations_5295_, uint8_t v_whnfType_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5292_, v_maxFVars_x3f_5293_, v_k_5294_, v_cleanupAnnotations_5295_, v_whnfType_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5303_, lean_object* v_type_5304_, lean_object* v_maxFVars_x3f_5305_, lean_object* v_k_5306_, lean_object* v_cleanupAnnotations_5307_, lean_object* v_whnfType_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5314_; uint8_t v_whnfType_boxed_5315_; lean_object* v_res_5316_; 
v_cleanupAnnotations_boxed_5314_ = lean_unbox(v_cleanupAnnotations_5307_);
v_whnfType_boxed_5315_ = lean_unbox(v_whnfType_5308_);
v_res_5316_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5303_, v_type_5304_, v_maxFVars_x3f_5305_, v_k_5306_, v_cleanupAnnotations_boxed_5314_, v_whnfType_boxed_5315_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
return v_res_5316_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5317_, lean_object* v_as_5318_, size_t v_i_5319_, size_t v_stop_5320_){
_start:
{
uint8_t v___x_5321_; 
v___x_5321_ = lean_usize_dec_eq(v_i_5319_, v_stop_5320_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; uint8_t v___x_5323_; 
v___x_5322_ = lean_array_uget_borrowed(v_as_5318_, v_i_5319_);
v___x_5323_ = lean_expr_eqv(v_a_5317_, v___x_5322_);
if (v___x_5323_ == 0)
{
size_t v___x_5324_; size_t v___x_5325_; 
v___x_5324_ = ((size_t)1ULL);
v___x_5325_ = lean_usize_add(v_i_5319_, v___x_5324_);
v_i_5319_ = v___x_5325_;
goto _start;
}
else
{
return v___x_5323_;
}
}
else
{
uint8_t v___x_5327_; 
v___x_5327_ = 0;
return v___x_5327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5328_, lean_object* v_as_5329_, lean_object* v_i_5330_, lean_object* v_stop_5331_){
_start:
{
size_t v_i_boxed_5332_; size_t v_stop_boxed_5333_; uint8_t v_res_5334_; lean_object* v_r_5335_; 
v_i_boxed_5332_ = lean_unbox_usize(v_i_5330_);
lean_dec(v_i_5330_);
v_stop_boxed_5333_ = lean_unbox_usize(v_stop_5331_);
lean_dec(v_stop_5331_);
v_res_5334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5328_, v_as_5329_, v_i_boxed_5332_, v_stop_boxed_5333_);
lean_dec_ref(v_as_5329_);
lean_dec_ref(v_a_5328_);
v_r_5335_ = lean_box(v_res_5334_);
return v_r_5335_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5336_, lean_object* v_a_5337_){
_start:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; uint8_t v___x_5340_; 
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = lean_array_get_size(v_as_5336_);
v___x_5340_ = lean_nat_dec_lt(v___x_5338_, v___x_5339_);
if (v___x_5340_ == 0)
{
return v___x_5340_;
}
else
{
size_t v___x_5341_; size_t v___x_5342_; uint8_t v___x_5343_; 
v___x_5341_ = ((size_t)0ULL);
v___x_5342_ = lean_usize_of_nat(v___x_5339_);
v___x_5343_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5337_, v_as_5336_, v___x_5341_, v___x_5342_);
return v___x_5343_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5344_, lean_object* v_a_5345_){
_start:
{
uint8_t v_res_5346_; lean_object* v_r_5347_; 
v_res_5346_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5344_, v_a_5345_);
lean_dec_ref(v_a_5345_);
lean_dec_ref(v_as_5344_);
v_r_5347_ = lean_box(v_res_5346_);
return v_r_5347_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5348_, lean_object* v_e_5349_){
_start:
{
uint8_t v___x_5350_; lean_object* v_d_5352_; lean_object* v_b_5353_; 
v___x_5350_ = l_Lean_Expr_hasFVar(v_e_5349_);
if (v___x_5350_ == 0)
{
lean_dec_ref(v_e_5349_);
return v___x_5350_;
}
else
{
switch(lean_obj_tag(v_e_5349_))
{
case 7:
{
lean_object* v_binderType_5356_; lean_object* v_body_5357_; 
v_binderType_5356_ = lean_ctor_get(v_e_5349_, 1);
lean_inc_ref(v_binderType_5356_);
v_body_5357_ = lean_ctor_get(v_e_5349_, 2);
lean_inc_ref(v_body_5357_);
lean_dec_ref_known(v_e_5349_, 3);
v_d_5352_ = v_binderType_5356_;
v_b_5353_ = v_body_5357_;
goto v___jp_5351_;
}
case 6:
{
lean_object* v_binderType_5358_; lean_object* v_body_5359_; 
v_binderType_5358_ = lean_ctor_get(v_e_5349_, 1);
lean_inc_ref(v_binderType_5358_);
v_body_5359_ = lean_ctor_get(v_e_5349_, 2);
lean_inc_ref(v_body_5359_);
lean_dec_ref_known(v_e_5349_, 3);
v_d_5352_ = v_binderType_5358_;
v_b_5353_ = v_body_5359_;
goto v___jp_5351_;
}
case 10:
{
lean_object* v_expr_5360_; 
v_expr_5360_ = lean_ctor_get(v_e_5349_, 1);
lean_inc_ref(v_expr_5360_);
lean_dec_ref_known(v_e_5349_, 2);
v_e_5349_ = v_expr_5360_;
goto _start;
}
case 8:
{
lean_object* v_type_5362_; lean_object* v_value_5363_; lean_object* v_body_5364_; uint8_t v___x_5365_; 
v_type_5362_ = lean_ctor_get(v_e_5349_, 1);
lean_inc_ref(v_type_5362_);
v_value_5363_ = lean_ctor_get(v_e_5349_, 2);
lean_inc_ref(v_value_5363_);
v_body_5364_ = lean_ctor_get(v_e_5349_, 3);
lean_inc_ref(v_body_5364_);
lean_dec_ref_known(v_e_5349_, 4);
v___x_5365_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5348_, v_type_5362_);
if (v___x_5365_ == 0)
{
uint8_t v___x_5366_; 
v___x_5366_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5348_, v_value_5363_);
if (v___x_5366_ == 0)
{
v_e_5349_ = v_body_5364_;
goto _start;
}
else
{
lean_dec_ref(v_body_5364_);
return v___x_5350_;
}
}
else
{
lean_dec_ref(v_body_5364_);
lean_dec_ref(v_value_5363_);
return v___x_5350_;
}
}
case 5:
{
lean_object* v_fn_5368_; lean_object* v_arg_5369_; uint8_t v___x_5370_; 
v_fn_5368_ = lean_ctor_get(v_e_5349_, 0);
lean_inc_ref(v_fn_5368_);
v_arg_5369_ = lean_ctor_get(v_e_5349_, 1);
lean_inc_ref(v_arg_5369_);
lean_dec_ref_known(v_e_5349_, 2);
v___x_5370_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5348_, v_fn_5368_);
if (v___x_5370_ == 0)
{
v_e_5349_ = v_arg_5369_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5369_);
return v___x_5350_;
}
}
case 11:
{
lean_object* v_struct_5372_; 
v_struct_5372_ = lean_ctor_get(v_e_5349_, 2);
lean_inc_ref(v_struct_5372_);
lean_dec_ref_known(v_e_5349_, 3);
v_e_5349_ = v_struct_5372_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_fvarId_5374_ = lean_ctor_get(v_e_5349_, 0);
lean_inc(v_fvarId_5374_);
lean_dec_ref_known(v_e_5349_, 1);
v___x_5375_ = l_Lean_Expr_fvar___override(v_fvarId_5374_);
v___x_5376_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5348_, v___x_5375_);
lean_dec_ref(v___x_5375_);
return v___x_5376_;
}
default: 
{
uint8_t v___x_5377_; 
lean_dec_ref(v_e_5349_);
v___x_5377_ = 0;
return v___x_5377_;
}
}
}
v___jp_5351_:
{
uint8_t v___x_5354_; 
v___x_5354_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5348_, v_d_5352_);
if (v___x_5354_ == 0)
{
v_e_5349_ = v_b_5353_;
goto _start;
}
else
{
lean_dec_ref(v_b_5353_);
return v___x_5350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5378_, lean_object* v_e_5379_){
_start:
{
uint8_t v_res_5380_; lean_object* v_r_5381_; 
v_res_5380_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5378_, v_e_5379_);
lean_dec_ref(v_xs_5378_);
v_r_5381_ = lean_box(v_res_5380_);
return v_r_5381_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5384_ = l_Lean_stringToMessageData(v___x_5383_);
return v___x_5384_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5387_ = l_Lean_stringToMessageData(v___x_5386_);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5388_, lean_object* v_type_5389_, lean_object* v_as_5390_, size_t v_sz_5391_, size_t v_i_5392_, lean_object* v_b_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v_a_5400_; uint8_t v___x_5404_; 
v___x_5404_ = lean_usize_dec_lt(v_i_5392_, v_sz_5391_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5405_; 
lean_dec_ref(v_type_5389_);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_b_5393_);
return v___x_5405_;
}
else
{
lean_object* v___x_5406_; lean_object* v_a_5407_; uint8_t v___x_5408_; 
v___x_5406_ = lean_box(0);
v_a_5407_ = lean_array_uget_borrowed(v_as_5390_, v_i_5392_);
lean_inc(v_a_5407_);
v___x_5408_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5388_, v_a_5407_);
if (v___x_5408_ == 0)
{
v_a_5400_ = v___x_5406_;
goto v___jp_5399_;
}
else
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5407_);
v___x_5410_ = l_Lean_MessageData_ofExpr(v_a_5407_);
v___x_5411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5411_);
lean_ctor_set(v___x_5413_, 1, v___x_5412_);
lean_inc_ref(v_type_5389_);
v___x_5414_ = l_Lean_MessageData_ofExpr(v_type_5389_);
v___x_5415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5415_, 0, v___x_5413_);
lean_ctor_set(v___x_5415_, 1, v___x_5414_);
v___x_5416_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5415_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_dec_ref_known(v___x_5416_, 1);
v_a_5400_ = v___x_5406_;
goto v___jp_5399_;
}
else
{
lean_dec_ref(v_type_5389_);
return v___x_5416_;
}
}
}
v___jp_5399_:
{
size_t v___x_5401_; size_t v___x_5402_; 
v___x_5401_ = ((size_t)1ULL);
v___x_5402_ = lean_usize_add(v_i_5392_, v___x_5401_);
v_i_5392_ = v___x_5402_;
v_b_5393_ = v_a_5400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5417_, lean_object* v_type_5418_, lean_object* v_as_5419_, lean_object* v_sz_5420_, lean_object* v_i_5421_, lean_object* v_b_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
size_t v_sz_boxed_5428_; size_t v_i_boxed_5429_; lean_object* v_res_5430_; 
v_sz_boxed_5428_ = lean_unbox_usize(v_sz_5420_);
lean_dec(v_sz_5420_);
v_i_boxed_5429_ = lean_unbox_usize(v_i_5421_);
lean_dec(v_i_5421_);
v_res_5430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5417_, v_type_5418_, v_as_5419_, v_sz_boxed_5428_, v_i_boxed_5429_, v_b_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec_ref(v_as_5419_);
lean_dec_ref(v_xs_5417_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5431_, size_t v_i_5432_, lean_object* v_bs_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
uint8_t v___x_5439_; 
v___x_5439_ = lean_usize_dec_lt(v_i_5432_, v_sz_5431_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5440_; 
v___x_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5440_, 0, v_bs_5433_);
return v___x_5440_;
}
else
{
lean_object* v_v_5441_; lean_object* v___x_5442_; lean_object* v_bs_x27_5443_; lean_object* v___x_5444_; 
v_v_5441_ = lean_array_uget(v_bs_5433_, v_i_5432_);
v___x_5442_ = lean_unsigned_to_nat(0u);
v_bs_x27_5443_ = lean_array_uset(v_bs_5433_, v_i_5432_, v___x_5442_);
lean_inc(v___y_5437_);
lean_inc_ref(v___y_5436_);
lean_inc(v___y_5435_);
lean_inc_ref(v___y_5434_);
v___x_5444_ = lean_infer_type(v_v_5441_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; size_t v___x_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref_known(v___x_5444_, 1);
v___x_5446_ = ((size_t)1ULL);
v___x_5447_ = lean_usize_add(v_i_5432_, v___x_5446_);
v___x_5448_ = lean_array_uset(v_bs_x27_5443_, v_i_5432_, v_a_5445_);
v_i_5432_ = v___x_5447_;
v_bs_5433_ = v___x_5448_;
goto _start;
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_dec_ref(v_bs_x27_5443_);
v_a_5450_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5444_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5444_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5458_, lean_object* v_i_5459_, lean_object* v_bs_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_){
_start:
{
size_t v_sz_boxed_5466_; size_t v_i_boxed_5467_; lean_object* v_res_5468_; 
v_sz_boxed_5466_ = lean_unbox_usize(v_sz_5458_);
lean_dec(v_sz_5458_);
v_i_boxed_5467_ = lean_unbox_usize(v_i_5459_);
lean_dec(v_i_5459_);
v_res_5468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5466_, v_i_boxed_5467_, v_bs_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
return v_res_5468_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5471_ = l_Lean_stringToMessageData(v___x_5470_);
return v___x_5471_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5474_ = l_Lean_stringToMessageData(v___x_5473_);
return v___x_5474_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5476_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5477_ = l_Lean_stringToMessageData(v___x_5476_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5478_, lean_object* v_n_5479_, lean_object* v_xs_5480_, lean_object* v_x_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5511_ = lean_array_get_size(v_xs_5480_);
v___x_5512_ = lean_nat_dec_eq(v___x_5511_, v_n_5479_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_dec_ref(v_xs_5480_);
v___x_5513_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5514_ = l_Lean_MessageData_ofExpr(v_type_5478_);
v___x_5515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5513_);
lean_ctor_set(v___x_5515_, 1, v___x_5514_);
v___x_5516_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5515_);
lean_ctor_set(v___x_5517_, 1, v___x_5516_);
v___x_5518_ = l_Nat_reprFast(v_n_5479_);
v___x_5519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5518_);
v___x_5520_ = l_Lean_MessageData_ofFormat(v___x_5519_);
v___x_5521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5517_);
lean_ctor_set(v___x_5521_, 1, v___x_5520_);
v___x_5522_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5521_);
lean_ctor_set(v___x_5523_, 1, v___x_5522_);
v___x_5524_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5523_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5524_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5524_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
else
{
lean_dec(v_n_5479_);
goto v___jp_5487_;
}
v___jp_5487_:
{
size_t v_sz_5488_; size_t v___x_5489_; lean_object* v___x_5490_; 
v_sz_5488_ = lean_array_size(v_xs_5480_);
v___x_5489_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5480_);
v___x_5490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5488_, v___x_5489_, v_xs_5480_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; size_t v_sz_5493_; lean_object* v___x_5494_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5492_ = lean_box(0);
v_sz_5493_ = lean_array_size(v_a_5491_);
v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5480_, v_type_5478_, v_a_5491_, v_sz_5493_, v___x_5489_, v___x_5492_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
lean_dec_ref(v_xs_5480_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5501_ == 0)
{
lean_object* v_unused_5502_; 
v_unused_5502_ = lean_ctor_get(v___x_5494_, 0);
lean_dec(v_unused_5502_);
v___x_5496_ = v___x_5494_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_dec(v___x_5494_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 0, v_a_5491_);
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5491_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
lean_dec(v_a_5491_);
v_a_5503_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5494_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5494_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5480_);
lean_dec_ref(v_type_5478_);
return v___x_5490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5533_, lean_object* v_n_5534_, lean_object* v_xs_5535_, lean_object* v_x_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5533_, v_n_5534_, v_xs_5535_, v_x_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec_ref(v_x_5536_);
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5543_, lean_object* v_type_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_){
_start:
{
lean_object* v___f_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; lean_object* v___x_5553_; 
lean_inc(v_n_5543_);
lean_inc_ref(v_type_5544_);
v___f_5550_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5550_, 0, v_type_5544_);
lean_closure_set(v___f_5550_, 1, v_n_5543_);
v___x_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5551_, 0, v_n_5543_);
v___x_5552_ = 0;
v___x_5553_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5544_, v___x_5551_, v___f_5550_, v___x_5552_, v___x_5552_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
return v___x_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5554_, lean_object* v_type_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_Lean_Meta_arrowDomainsN(v_n_5554_, v_type_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_);
lean_dec(v_a_5559_);
lean_dec_ref(v_a_5558_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5562_, lean_object* v_e_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_){
_start:
{
lean_object* v___x_5569_; 
lean_inc(v_a_5567_);
lean_inc_ref(v_a_5566_);
lean_inc(v_a_5565_);
lean_inc_ref(v_a_5564_);
v___x_5569_ = lean_infer_type(v_e_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
if (lean_obj_tag(v___x_5569_) == 0)
{
lean_object* v_a_5570_; lean_object* v___x_5571_; 
v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
lean_inc(v_a_5570_);
lean_dec_ref_known(v___x_5569_, 1);
v___x_5571_ = l_Lean_Meta_arrowDomainsN(v_n_5562_, v_a_5570_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_);
return v___x_5571_;
}
else
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5579_; 
lean_dec(v_n_5562_);
v_a_5572_ = lean_ctor_get(v___x_5569_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5574_ = v___x_5569_;
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5569_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v___x_5577_; 
if (v_isShared_5575_ == 0)
{
v___x_5577_ = v___x_5574_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5580_, lean_object* v_e_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_){
_start:
{
lean_object* v_res_5587_; 
v_res_5587_ = l_Lean_Meta_inferArgumentTypesN(v_n_5580_, v_e_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_);
lean_dec(v_a_5585_);
lean_dec_ref(v_a_5584_);
lean_dec(v_a_5583_);
lean_dec_ref(v_a_5582_);
return v_res_5587_;
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
