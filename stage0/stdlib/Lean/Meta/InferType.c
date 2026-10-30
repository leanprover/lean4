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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
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
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*);
uint8_t lean_expr_equal_budgeted(lean_object*, lean_object*, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected bound variable "};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_309_ = lean_unsigned_to_nat(1906u);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(lean_object* v_a_2472_, lean_object* v_b_2473_){
_start:
{
lean_object* v_expr_2474_; uint64_t v_configKey_2475_; lean_object* v_expr_2476_; uint64_t v_configKey_2477_; uint64_t v___x_2478_; uint64_t v___x_2479_; uint64_t v___x_2480_; uint64_t v___x_2481_; uint8_t v___x_2482_; 
v_expr_2474_ = lean_ctor_get(v_a_2472_, 0);
v_configKey_2475_ = lean_ctor_get_uint64(v_a_2472_, sizeof(void*)*1);
v_expr_2476_ = lean_ctor_get(v_b_2473_, 0);
v_configKey_2477_ = lean_ctor_get_uint64(v_b_2473_, sizeof(void*)*1);
v___x_2478_ = l_Lean_Expr_hash(v_expr_2474_);
v___x_2479_ = lean_uint64_mix_hash(v___x_2478_, v_configKey_2475_);
v___x_2480_ = l_Lean_Expr_hash(v_expr_2476_);
v___x_2481_ = lean_uint64_mix_hash(v___x_2480_, v_configKey_2477_);
v___x_2482_ = lean_uint64_dec_eq(v___x_2479_, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0___boxed(lean_object* v_a_2483_, lean_object* v_b_2484_){
_start:
{
uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_res_2485_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(v_a_2483_, v_b_2484_);
lean_dec_ref(v_b_2484_);
lean_dec_ref(v_a_2483_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_instMonadEIO___redArg();
return v___x_2487_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2489_ = l_StateRefT_x27_instMonad___redArg(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_instMonadExceptOfEIO___redArg();
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___f_2494_; 
v___x_2493_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2494_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2494_, 0, v___x_2493_);
return v___f_2494_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___f_2496_; 
v___x_2495_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2496_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2496_, 0, v___x_2495_);
return v___f_2496_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; 
v___f_2497_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2498_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___f_2498_);
lean_ctor_set(v___x_2499_, 1, v___f_2497_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___f_2501_; 
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2501_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2501_, 0, v___x_2500_);
return v___f_2501_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___f_2503_; 
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2503_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2503_, 0, v___x_2502_);
return v___f_2503_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
v___f_2504_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2505_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___f_2505_);
lean_ctor_set(v___x_2506_, 1, v___f_2504_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2509_, lean_object* v_inferType_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
uint8_t v_cacheInferType_2555_; 
v_cacheInferType_2555_ = lean_ctor_get_uint8(v_a_2511_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2555_ == 0)
{
lean_dec_ref(v_e_2509_);
goto v___jp_2516_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = l_Lean_Expr_hasMVar(v_e_2509_);
if (v___x_2556_ == 0)
{
lean_object* v___f_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___f_2557_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2559_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2509_, v_a_2511_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2687_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2687_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2687_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2641_; lean_object* v_cache_2642_; lean_object* v_inferType_2643_; lean_object* v___x_2644_; 
v___x_2641_ = lean_st_ref_get(v_a_2512_);
v_cache_2642_ = lean_ctor_get(v___x_2641_, 1);
lean_inc_ref(v_cache_2642_);
lean_dec(v___x_2641_);
v_inferType_2643_ = lean_ctor_get(v_cache_2642_, 0);
lean_inc_ref(v_inferType_2643_);
lean_dec_ref(v_cache_2642_);
lean_inc(v_a_2560_);
v___x_2644_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_2557_, v___x_2558_, v_inferType_2643_, v_a_2560_);
if (lean_obj_tag(v___x_2644_) == 1)
{
lean_object* v_val_2645_; lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v_expr_2648_; uint64_t v_configKey_2649_; lean_object* v_expr_2650_; uint64_t v_configKey_2651_; uint8_t v___x_2652_; 
v_val_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_val_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v_fst_2646_ = lean_ctor_get(v_val_2645_, 0);
lean_inc(v_fst_2646_);
v_snd_2647_ = lean_ctor_get(v_val_2645_, 1);
lean_inc(v_snd_2647_);
lean_dec(v_val_2645_);
v_expr_2648_ = lean_ctor_get(v_a_2560_, 0);
v_configKey_2649_ = lean_ctor_get_uint64(v_a_2560_, sizeof(void*)*1);
v_expr_2650_ = lean_ctor_get(v_fst_2646_, 0);
lean_inc_ref(v_expr_2650_);
v_configKey_2651_ = lean_ctor_get_uint64(v_fst_2646_, sizeof(void*)*1);
lean_dec(v_fst_2646_);
v___x_2652_ = lean_uint64_dec_eq(v_configKey_2649_, v_configKey_2651_);
if (v___x_2652_ == 0)
{
lean_dec_ref(v_expr_2650_);
lean_dec(v_snd_2647_);
lean_dec_ref(v_inferType_2643_);
lean_del_object(v___x_2562_);
goto v___jp_2605_;
}
else
{
size_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = ((size_t)64ULL);
v___x_2654_ = lean_expr_equal_budgeted(v_expr_2648_, v_expr_2650_, v___x_2653_);
lean_dec_ref(v_expr_2650_);
switch(v___x_2654_)
{
case 0:
{
lean_dec(v_snd_2647_);
lean_dec_ref(v_inferType_2643_);
lean_del_object(v___x_2562_);
goto v___jp_2605_;
}
case 1:
{
lean_object* v___x_2656_; 
lean_dec_ref(v_inferType_2643_);
lean_dec(v_a_2560_);
lean_dec_ref(v_inferType_2510_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_snd_2647_);
v___x_2656_ = v___x_2562_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_snd_2647_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
default: 
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v_cache_2660_; lean_object* v_mctx_2661_; lean_object* v_zetaDeltaFVarIds_2662_; lean_object* v_postponed_2663_; lean_object* v_diag_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_snd_2647_);
lean_del_object(v___x_2562_);
lean_inc(v_a_2560_);
v___x_2658_ = l_Lean_PersistentHashMap_erase___redArg(v___f_2557_, v___x_2558_, v_inferType_2643_, v_a_2560_);
v___x_2659_ = lean_st_ref_take(v_a_2512_);
v_cache_2660_ = lean_ctor_get(v___x_2659_, 1);
v_mctx_2661_ = lean_ctor_get(v___x_2659_, 0);
v_zetaDeltaFVarIds_2662_ = lean_ctor_get(v___x_2659_, 2);
v_postponed_2663_ = lean_ctor_get(v___x_2659_, 3);
v_diag_2664_ = lean_ctor_get(v___x_2659_, 4);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2666_ = v___x_2659_;
v_isShared_2667_ = v_isSharedCheck_2686_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_diag_2664_);
lean_inc(v_postponed_2663_);
lean_inc(v_zetaDeltaFVarIds_2662_);
lean_inc(v_cache_2660_);
lean_inc(v_mctx_2661_);
lean_dec(v___x_2659_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2686_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_funInfo_2668_; lean_object* v_synthInstance_2669_; lean_object* v_whnf_2670_; lean_object* v_defEqTrans_2671_; lean_object* v_defEqPerm_2672_; lean_object* v_isUnitLike_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2684_; 
v_funInfo_2668_ = lean_ctor_get(v_cache_2660_, 1);
v_synthInstance_2669_ = lean_ctor_get(v_cache_2660_, 2);
v_whnf_2670_ = lean_ctor_get(v_cache_2660_, 3);
v_defEqTrans_2671_ = lean_ctor_get(v_cache_2660_, 4);
v_defEqPerm_2672_ = lean_ctor_get(v_cache_2660_, 5);
v_isUnitLike_2673_ = lean_ctor_get(v_cache_2660_, 6);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_cache_2660_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v_cache_2660_, 0);
lean_dec(v_unused_2685_);
v___x_2675_ = v_cache_2660_;
v_isShared_2676_ = v_isSharedCheck_2684_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_isUnitLike_2673_);
lean_inc(v_defEqPerm_2672_);
lean_inc(v_defEqTrans_2671_);
lean_inc(v_whnf_2670_);
lean_inc(v_synthInstance_2669_);
lean_inc(v_funInfo_2668_);
lean_dec(v_cache_2660_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2684_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2658_);
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_funInfo_2668_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_synthInstance_2669_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_whnf_2670_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_defEqTrans_2671_);
lean_ctor_set(v_reuseFailAlloc_2683_, 5, v_defEqPerm_2672_);
lean_ctor_set(v_reuseFailAlloc_2683_, 6, v_isUnitLike_2673_);
v___x_2678_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2678_);
v___x_2680_ = v___x_2666_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_mctx_2661_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_zetaDeltaFVarIds_2662_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_postponed_2663_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_diag_2664_);
v___x_2680_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_st_ref_put(v_a_2512_, v___x_2680_);
goto v___jp_2605_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2644_);
lean_dec_ref(v_inferType_2643_);
lean_del_object(v___x_2562_);
goto v___jp_2605_;
}
v___jp_2564_:
{
lean_object* v___x_2565_; 
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2511_);
v___x_2565_ = lean_apply_5(v_inferType_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; uint8_t v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
v___x_2567_ = l_Lean_Expr_hasMVar(v_a_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2603_; 
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2604_);
v___x_2569_ = v___x_2565_;
v_isShared_2570_ = v_isSharedCheck_2603_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2565_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2603_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v_cache_2572_; lean_object* v_mctx_2573_; lean_object* v_zetaDeltaFVarIds_2574_; lean_object* v_postponed_2575_; lean_object* v_diag_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2602_; 
v___x_2571_ = lean_st_ref_take(v_a_2512_);
v_cache_2572_ = lean_ctor_get(v___x_2571_, 1);
v_mctx_2573_ = lean_ctor_get(v___x_2571_, 0);
v_zetaDeltaFVarIds_2574_ = lean_ctor_get(v___x_2571_, 2);
v_postponed_2575_ = lean_ctor_get(v___x_2571_, 3);
v_diag_2576_ = lean_ctor_get(v___x_2571_, 4);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2578_ = v___x_2571_;
v_isShared_2579_ = v_isSharedCheck_2602_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_diag_2576_);
lean_inc(v_postponed_2575_);
lean_inc(v_zetaDeltaFVarIds_2574_);
lean_inc(v_cache_2572_);
lean_inc(v_mctx_2573_);
lean_dec(v___x_2571_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2602_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_inferType_2580_; lean_object* v_funInfo_2581_; lean_object* v_synthInstance_2582_; lean_object* v_whnf_2583_; lean_object* v_defEqTrans_2584_; lean_object* v_defEqPerm_2585_; lean_object* v_isUnitLike_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2601_; 
v_inferType_2580_ = lean_ctor_get(v_cache_2572_, 0);
v_funInfo_2581_ = lean_ctor_get(v_cache_2572_, 1);
v_synthInstance_2582_ = lean_ctor_get(v_cache_2572_, 2);
v_whnf_2583_ = lean_ctor_get(v_cache_2572_, 3);
v_defEqTrans_2584_ = lean_ctor_get(v_cache_2572_, 4);
v_defEqPerm_2585_ = lean_ctor_get(v_cache_2572_, 5);
v_isUnitLike_2586_ = lean_ctor_get(v_cache_2572_, 6);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_cache_2572_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2588_ = v_cache_2572_;
v_isShared_2589_ = v_isSharedCheck_2601_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_isUnitLike_2586_);
lean_inc(v_defEqPerm_2585_);
lean_inc(v_defEqTrans_2584_);
lean_inc(v_whnf_2583_);
lean_inc(v_synthInstance_2582_);
lean_inc(v_funInfo_2581_);
lean_inc(v_inferType_2580_);
lean_dec(v_cache_2572_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2601_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_inc(v_a_2566_);
v___x_2590_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2557_, v___x_2558_, v_inferType_2580_, v_a_2560_, v_a_2566_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2590_);
v___x_2592_ = v___x_2588_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_funInfo_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_synthInstance_2582_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_whnf_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_defEqTrans_2584_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_defEqPerm_2585_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_isUnitLike_2586_);
v___x_2592_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___x_2592_);
v___x_2594_ = v___x_2578_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_mctx_2573_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_zetaDeltaFVarIds_2574_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_postponed_2575_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_diag_2576_);
v___x_2594_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_st_ref_put(v_a_2512_, v___x_2594_);
if (v_isShared_2570_ == 0)
{
v___x_2597_ = v___x_2569_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2566_);
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
}
}
else
{
lean_dec(v_a_2566_);
lean_dec(v_a_2560_);
return v___x_2565_;
}
}
else
{
lean_dec(v_a_2560_);
return v___x_2565_;
}
}
v___jp_2605_:
{
lean_object* v___x_2606_; lean_object* v_toApplicative_2607_; lean_object* v_toFunctor_2608_; lean_object* v_toSeq_2609_; lean_object* v_toSeqLeft_2610_; lean_object* v_toSeqRight_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_toCold_2627_; lean_object* v_cancelTk_x3f_2628_; 
v___x_2606_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2607_ = lean_ctor_get(v___x_2606_, 0);
v_toFunctor_2608_ = lean_ctor_get(v_toApplicative_2607_, 0);
v_toSeq_2609_ = lean_ctor_get(v_toApplicative_2607_, 2);
v_toSeqLeft_2610_ = lean_ctor_get(v_toApplicative_2607_, 3);
v_toSeqRight_2611_ = lean_ctor_get(v_toApplicative_2607_, 4);
v___f_2612_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2613_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2608_, 2);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toFunctor_2608_);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toFunctor_2608_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___f_2614_);
lean_ctor_set(v___x_2616_, 1, v___f_2615_);
lean_inc(v_toSeqRight_2611_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toSeqRight_2611_);
lean_inc(v_toSeqLeft_2610_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeqLeft_2610_);
lean_inc(v_toSeq_2609_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeq_2609_);
v___x_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___f_2612_);
lean_ctor_set(v___x_2620_, 2, v___f_2619_);
lean_ctor_set(v___x_2620_, 3, v___f_2618_);
lean_ctor_set(v___x_2620_, 4, v___f_2617_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___f_2613_);
v___x_2622_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2623_ = l_Lean_Core_instMonadRefCoreM;
v___x_2624_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2625_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2624_, v___x_2621_);
v___x_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2622_);
lean_ctor_set(v___x_2626_, 1, v___x_2623_);
lean_ctor_set(v___x_2626_, 2, v___x_2625_);
v_toCold_2627_ = lean_ctor_get(v_a_2513_, 0);
v_cancelTk_x3f_2628_ = lean_ctor_get(v_toCold_2627_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2628_) == 1)
{
lean_object* v_val_2629_; uint8_t v___x_2630_; 
v_val_2629_ = lean_ctor_get(v_cancelTk_x3f_2628_, 0);
v___x_2630_ = l_IO_CancelToken_isSet(v_val_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2564_;
}
else
{
lean_object* v___x_4224__overap_2631_; lean_object* v___x_2632_; 
v___x_4224__overap_2631_ = l_Lean_throwInterruptException___redArg(v___x_2626_);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
v___x_2632_ = lean_apply_3(v___x_4224__overap_2631_, v_a_2513_, v_a_2514_, lean_box(0));
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_dec_ref_known(v___x_2632_, 1);
goto v___jp_2564_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2560_);
lean_dec_ref(v_inferType_2510_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2626_, 3);
goto v___jp_2564_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v_inferType_2510_);
v_a_2688_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2559_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2559_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_dec_ref(v_e_2509_);
goto v___jp_2516_;
}
}
v___jp_2516_:
{
lean_object* v___x_2517_; lean_object* v_toApplicative_2518_; lean_object* v_toFunctor_2519_; lean_object* v_toSeq_2520_; lean_object* v_toSeqLeft_2521_; lean_object* v_toSeqRight_2522_; lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___f_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___f_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_toCold_2538_; lean_object* v_cancelTk_x3f_2539_; 
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2518_ = lean_ctor_get(v___x_2517_, 0);
v_toFunctor_2519_ = lean_ctor_get(v_toApplicative_2518_, 0);
v_toSeq_2520_ = lean_ctor_get(v_toApplicative_2518_, 2);
v_toSeqLeft_2521_ = lean_ctor_get(v_toApplicative_2518_, 3);
v_toSeqRight_2522_ = lean_ctor_get(v_toApplicative_2518_, 4);
v___f_2523_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2524_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2519_, 2);
v___f_2525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2525_, 0, v_toFunctor_2519_);
v___f_2526_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2526_, 0, v_toFunctor_2519_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___f_2525_);
lean_ctor_set(v___x_2527_, 1, v___f_2526_);
lean_inc(v_toSeqRight_2522_);
v___f_2528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2528_, 0, v_toSeqRight_2522_);
lean_inc(v_toSeqLeft_2521_);
v___f_2529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2529_, 0, v_toSeqLeft_2521_);
lean_inc(v_toSeq_2520_);
v___f_2530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2530_, 0, v_toSeq_2520_);
v___x_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2527_);
lean_ctor_set(v___x_2531_, 1, v___f_2523_);
lean_ctor_set(v___x_2531_, 2, v___f_2530_);
lean_ctor_set(v___x_2531_, 3, v___f_2529_);
lean_ctor_set(v___x_2531_, 4, v___f_2528_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___f_2524_);
v___x_2533_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2534_ = l_Lean_Core_instMonadRefCoreM;
v___x_2535_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2536_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2535_, v___x_2532_);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2533_);
lean_ctor_set(v___x_2537_, 1, v___x_2534_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
v_toCold_2538_ = lean_ctor_get(v_a_2513_, 0);
v_cancelTk_x3f_2539_ = lean_ctor_get(v_toCold_2538_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2539_) == 1)
{
lean_object* v_val_2540_; uint8_t v___x_2541_; 
v_val_2540_ = lean_ctor_get(v_cancelTk_x3f_2539_, 0);
v___x_2541_ = l_IO_CancelToken_isSet(v_val_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref_known(v___x_2537_, 3);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2511_);
v___x_2542_ = lean_apply_5(v_inferType_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, lean_box(0));
return v___x_2542_;
}
else
{
lean_object* v___x_4199__overap_2543_; lean_object* v___x_2544_; 
v___x_4199__overap_2543_ = l_Lean_throwInterruptException___redArg(v___x_2537_);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
v___x_2544_ = lean_apply_3(v___x_4199__overap_2543_, v_a_2513_, v_a_2514_, lean_box(0));
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref_known(v___x_2544_, 1);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2511_);
v___x_2545_ = lean_apply_5(v_inferType_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, lean_box(0));
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_inferType_2510_);
v_a_2546_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2544_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2544_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
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
else
{
lean_object* v___x_2554_; 
lean_dec_ref_known(v___x_2537_, 3);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
lean_inc(v_a_2512_);
lean_inc_ref(v_a_2511_);
v___x_2554_ = lean_apply_5(v_inferType_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, lean_box(0));
return v___x_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2696_, lean_object* v_inferType_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2696_, v_inferType_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2756_; uint8_t v_beta_2757_; 
v___x_2756_ = l_Lean_Meta_Context_config(v___y_2705_);
v_beta_2757_ = lean_ctor_get_uint8(v___x_2756_, 13);
if (v_beta_2757_ == 0)
{
lean_dec_ref(v___x_2756_);
goto v___jp_2710_;
}
else
{
uint8_t v_iota_2758_; 
v_iota_2758_ = lean_ctor_get_uint8(v___x_2756_, 12);
if (v_iota_2758_ == 0)
{
lean_dec_ref(v___x_2756_);
goto v___jp_2710_;
}
else
{
uint8_t v_zeta_2759_; 
v_zeta_2759_ = lean_ctor_get_uint8(v___x_2756_, 15);
if (v_zeta_2759_ == 0)
{
lean_dec_ref(v___x_2756_);
goto v___jp_2710_;
}
else
{
uint8_t v_zetaHave_2760_; 
v_zetaHave_2760_ = lean_ctor_get_uint8(v___x_2756_, 18);
if (v_zetaHave_2760_ == 0)
{
lean_dec_ref(v___x_2756_);
goto v___jp_2710_;
}
else
{
uint8_t v_zetaDelta_2761_; 
v_zetaDelta_2761_ = lean_ctor_get_uint8(v___x_2756_, 16);
if (v_zetaDelta_2761_ == 0)
{
lean_dec_ref(v___x_2756_);
goto v___jp_2710_;
}
else
{
uint8_t v_etaStruct_2762_; uint8_t v_proj_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_etaStruct_2762_ = lean_ctor_get_uint8(v___x_2756_, 10);
v_proj_2763_ = lean_ctor_get_uint8(v___x_2756_, 14);
lean_dec_ref(v___x_2756_);
v___x_2764_ = lean_box(v_proj_2763_);
v___x_2765_ = lean_obj_tag_nat(v___x_2764_);
lean_dec(v___x_2764_);
v___x_2766_ = lean_unsigned_to_nat(2u);
v___x_2767_ = lean_nat_dec_eq(v___x_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
goto v___jp_2710_;
}
else
{
uint8_t v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = 0;
v___x_2769_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2762_, v___x_2768_);
if (v___x_2769_ == 0)
{
goto v___jp_2710_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_apply_5(v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, lean_box(0));
return v___x_2770_;
}
}
}
}
}
}
}
v___jp_2710_:
{
lean_object* v___x_2711_; uint8_t v_foApprox_2712_; uint8_t v_ctxApprox_2713_; uint8_t v_quasiPatternApprox_2714_; uint8_t v_constApprox_2715_; uint8_t v_isDefEqStuckEx_2716_; uint8_t v_unificationHints_2717_; uint8_t v_proofIrrelevance_2718_; uint8_t v_assignSyntheticOpaque_2719_; uint8_t v_offsetCnstrs_2720_; uint8_t v_transparency_2721_; uint8_t v_univApprox_2722_; uint8_t v_zetaUnused_2723_; uint8_t v_canUnfoldPredicateConfig_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2755_; 
v___x_2711_ = l_Lean_Meta_Context_config(v___y_2705_);
v_foApprox_2712_ = lean_ctor_get_uint8(v___x_2711_, 0);
v_ctxApprox_2713_ = lean_ctor_get_uint8(v___x_2711_, 1);
v_quasiPatternApprox_2714_ = lean_ctor_get_uint8(v___x_2711_, 2);
v_constApprox_2715_ = lean_ctor_get_uint8(v___x_2711_, 3);
v_isDefEqStuckEx_2716_ = lean_ctor_get_uint8(v___x_2711_, 4);
v_unificationHints_2717_ = lean_ctor_get_uint8(v___x_2711_, 5);
v_proofIrrelevance_2718_ = lean_ctor_get_uint8(v___x_2711_, 6);
v_assignSyntheticOpaque_2719_ = lean_ctor_get_uint8(v___x_2711_, 7);
v_offsetCnstrs_2720_ = lean_ctor_get_uint8(v___x_2711_, 8);
v_transparency_2721_ = lean_ctor_get_uint8(v___x_2711_, 9);
v_univApprox_2722_ = lean_ctor_get_uint8(v___x_2711_, 11);
v_zetaUnused_2723_ = lean_ctor_get_uint8(v___x_2711_, 17);
v_canUnfoldPredicateConfig_2724_ = lean_ctor_get_uint8(v___x_2711_, 19);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2726_ = v___x_2711_;
v_isShared_2727_ = v_isSharedCheck_2755_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v___x_2711_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2755_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint8_t v___x_2728_; uint8_t v___x_2729_; uint8_t v___x_2730_; lean_object* v___x_2732_; 
v___x_2728_ = 1;
v___x_2729_ = 0;
v___x_2730_ = 2;
if (v_isShared_2727_ == 0)
{
v___x_2732_ = v___x_2726_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 0, v_foApprox_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 1, v_ctxApprox_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 2, v_quasiPatternApprox_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 3, v_constApprox_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 4, v_isDefEqStuckEx_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 5, v_unificationHints_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 6, v_proofIrrelevance_2718_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 7, v_assignSyntheticOpaque_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 8, v_offsetCnstrs_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 9, v_transparency_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 11, v_univApprox_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 17, v_zetaUnused_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, 19, v_canUnfoldPredicateConfig_2724_);
v___x_2732_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
uint8_t v_trackZetaDelta_2733_; lean_object* v_zetaDeltaSet_2734_; lean_object* v_lctx_2735_; lean_object* v_localInstances_2736_; lean_object* v_defEqCtx_x3f_2737_; lean_object* v_synthPendingDepth_2738_; lean_object* v_customCanUnfoldPredicate_x3f_2739_; uint8_t v_univApprox_2740_; uint8_t v_inTypeClassResolution_2741_; uint8_t v_cacheInferType_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2752_; 
lean_ctor_set_uint8(v___x_2732_, 10, v___x_2729_);
lean_ctor_set_uint8(v___x_2732_, 12, v___x_2728_);
lean_ctor_set_uint8(v___x_2732_, 13, v___x_2728_);
lean_ctor_set_uint8(v___x_2732_, 14, v___x_2730_);
lean_ctor_set_uint8(v___x_2732_, 15, v___x_2728_);
lean_ctor_set_uint8(v___x_2732_, 16, v___x_2728_);
lean_ctor_set_uint8(v___x_2732_, 18, v___x_2728_);
v_trackZetaDelta_2733_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7);
v_zetaDeltaSet_2734_ = lean_ctor_get(v___y_2705_, 1);
v_lctx_2735_ = lean_ctor_get(v___y_2705_, 2);
v_localInstances_2736_ = lean_ctor_get(v___y_2705_, 3);
v_defEqCtx_x3f_2737_ = lean_ctor_get(v___y_2705_, 4);
v_synthPendingDepth_2738_ = lean_ctor_get(v___y_2705_, 5);
v_customCanUnfoldPredicate_x3f_2739_ = lean_ctor_get(v___y_2705_, 6);
v_univApprox_2740_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2741_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 2);
v_cacheInferType_2742_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*7 + 3);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___y_2705_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; 
v_unused_2753_ = lean_ctor_get(v___y_2705_, 0);
lean_dec(v_unused_2753_);
v___x_2744_ = v___y_2705_;
v_isShared_2745_ = v_isSharedCheck_2752_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2739_);
lean_inc(v_synthPendingDepth_2738_);
lean_inc(v_defEqCtx_x3f_2737_);
lean_inc(v_localInstances_2736_);
lean_inc(v_lctx_2735_);
lean_inc(v_zetaDeltaSet_2734_);
lean_dec(v___y_2705_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2752_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
uint64_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2746_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2732_);
v___x_2747_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2747_, 0, v___x_2732_);
lean_ctor_set_uint64(v___x_2747_, sizeof(void*)*1, v___x_2746_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2747_);
v___x_2749_ = v___x_2744_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_zetaDeltaSet_2734_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_lctx_2735_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_localInstances_2736_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v_defEqCtx_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2751_, 5, v_synthPendingDepth_2738_);
lean_ctor_set(v_reuseFailAlloc_2751_, 6, v_customCanUnfoldPredicate_x3f_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*7, v_trackZetaDelta_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*7 + 1, v_univApprox_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2751_, sizeof(void*)*7 + 3, v_cacheInferType_2742_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_apply_5(v_x_2704_, v___x_2749_, v___y_2706_, v___y_2707_, v___y_2708_, lean_box(0));
return v___x_2750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___y_2785_; lean_object* v___x_2802_; uint8_t v_transparency_2803_; uint8_t v___x_2804_; uint8_t v___x_2805_; 
v___x_2802_ = l_Lean_Meta_Context_config(v_a_2779_);
v_transparency_2803_ = lean_ctor_get_uint8(v___x_2802_, 9);
lean_dec_ref(v___x_2802_);
v___x_2804_ = 1;
v___x_2805_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2803_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
v___x_2806_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
v___y_2785_ = v___x_2806_;
goto v___jp_2784_;
}
else
{
lean_object* v_keyedConfig_2807_; uint8_t v_trackZetaDelta_2808_; lean_object* v_zetaDeltaSet_2809_; lean_object* v_lctx_2810_; lean_object* v_localInstances_2811_; lean_object* v_defEqCtx_x3f_2812_; lean_object* v_synthPendingDepth_2813_; lean_object* v_customCanUnfoldPredicate_x3f_2814_; uint8_t v_univApprox_2815_; uint8_t v_inTypeClassResolution_2816_; uint8_t v_cacheInferType_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_keyedConfig_2807_ = lean_ctor_get(v_a_2779_, 0);
v_trackZetaDelta_2808_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7);
v_zetaDeltaSet_2809_ = lean_ctor_get(v_a_2779_, 1);
v_lctx_2810_ = lean_ctor_get(v_a_2779_, 2);
v_localInstances_2811_ = lean_ctor_get(v_a_2779_, 3);
v_defEqCtx_x3f_2812_ = lean_ctor_get(v_a_2779_, 4);
v_synthPendingDepth_2813_ = lean_ctor_get(v_a_2779_, 5);
v_customCanUnfoldPredicate_x3f_2814_ = lean_ctor_get(v_a_2779_, 6);
v_univApprox_2815_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2816_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 2);
v_cacheInferType_2817_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2807_);
v___x_2818_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2804_, v_keyedConfig_2807_);
lean_inc(v_customCanUnfoldPredicate_x3f_2814_);
lean_inc(v_synthPendingDepth_2813_);
lean_inc(v_defEqCtx_x3f_2812_);
lean_inc_ref(v_localInstances_2811_);
lean_inc_ref(v_lctx_2810_);
lean_inc(v_zetaDeltaSet_2809_);
v___x_2819_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_zetaDeltaSet_2809_);
lean_ctor_set(v___x_2819_, 2, v_lctx_2810_);
lean_ctor_set(v___x_2819_, 3, v_localInstances_2811_);
lean_ctor_set(v___x_2819_, 4, v_defEqCtx_x3f_2812_);
lean_ctor_set(v___x_2819_, 5, v_synthPendingDepth_2813_);
lean_ctor_set(v___x_2819_, 6, v_customCanUnfoldPredicate_x3f_2814_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*7, v_trackZetaDelta_2808_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*7 + 1, v_univApprox_2815_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2816_);
lean_ctor_set_uint8(v___x_2819_, sizeof(void*)*7 + 3, v_cacheInferType_2817_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
v___x_2820_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2778_, v___x_2819_, v_a_2780_, v_a_2781_, v_a_2782_);
v___y_2785_ = v___x_2820_;
goto v___jp_2784_;
}
v___jp_2784_:
{
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___y_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___y_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___y_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___y_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___y_2785_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___y_2785_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___y_2785_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___y_2785_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2828_, lean_object* v_x_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v___y_2836_; lean_object* v___x_2853_; uint8_t v_transparency_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2853_ = l_Lean_Meta_Context_config(v_a_2830_);
v_transparency_2854_ = lean_ctor_get_uint8(v___x_2853_, 9);
lean_dec_ref(v___x_2853_);
v___x_2855_ = 1;
v___x_2856_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_inc(v_a_2833_);
lean_inc_ref(v_a_2832_);
lean_inc(v_a_2831_);
lean_inc_ref(v_a_2830_);
v___x_2857_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
v___y_2836_ = v___x_2857_;
goto v___jp_2835_;
}
else
{
lean_object* v_keyedConfig_2858_; uint8_t v_trackZetaDelta_2859_; lean_object* v_zetaDeltaSet_2860_; lean_object* v_lctx_2861_; lean_object* v_localInstances_2862_; lean_object* v_defEqCtx_x3f_2863_; lean_object* v_synthPendingDepth_2864_; lean_object* v_customCanUnfoldPredicate_x3f_2865_; uint8_t v_univApprox_2866_; uint8_t v_inTypeClassResolution_2867_; uint8_t v_cacheInferType_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_keyedConfig_2858_ = lean_ctor_get(v_a_2830_, 0);
v_trackZetaDelta_2859_ = lean_ctor_get_uint8(v_a_2830_, sizeof(void*)*7);
v_zetaDeltaSet_2860_ = lean_ctor_get(v_a_2830_, 1);
v_lctx_2861_ = lean_ctor_get(v_a_2830_, 2);
v_localInstances_2862_ = lean_ctor_get(v_a_2830_, 3);
v_defEqCtx_x3f_2863_ = lean_ctor_get(v_a_2830_, 4);
v_synthPendingDepth_2864_ = lean_ctor_get(v_a_2830_, 5);
v_customCanUnfoldPredicate_x3f_2865_ = lean_ctor_get(v_a_2830_, 6);
v_univApprox_2866_ = lean_ctor_get_uint8(v_a_2830_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2867_ = lean_ctor_get_uint8(v_a_2830_, sizeof(void*)*7 + 2);
v_cacheInferType_2868_ = lean_ctor_get_uint8(v_a_2830_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2858_);
v___x_2869_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2855_, v_keyedConfig_2858_);
lean_inc(v_customCanUnfoldPredicate_x3f_2865_);
lean_inc(v_synthPendingDepth_2864_);
lean_inc(v_defEqCtx_x3f_2863_);
lean_inc_ref(v_localInstances_2862_);
lean_inc_ref(v_lctx_2861_);
lean_inc(v_zetaDeltaSet_2860_);
v___x_2870_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v_zetaDeltaSet_2860_);
lean_ctor_set(v___x_2870_, 2, v_lctx_2861_);
lean_ctor_set(v___x_2870_, 3, v_localInstances_2862_);
lean_ctor_set(v___x_2870_, 4, v_defEqCtx_x3f_2863_);
lean_ctor_set(v___x_2870_, 5, v_synthPendingDepth_2864_);
lean_ctor_set(v___x_2870_, 6, v_customCanUnfoldPredicate_x3f_2865_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*7, v_trackZetaDelta_2859_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*7 + 1, v_univApprox_2866_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2867_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*7 + 3, v_cacheInferType_2868_);
lean_inc(v_a_2833_);
lean_inc_ref(v_a_2832_);
lean_inc(v_a_2831_);
v___x_2871_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2829_, v___x_2870_, v_a_2831_, v_a_2832_, v_a_2833_);
v___y_2836_ = v___x_2871_;
goto v___jp_2835_;
}
v___jp_2835_:
{
if (lean_obj_tag(v___y_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_a_2837_ = lean_ctor_get(v___y_2836_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___y_2836_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___y_2836_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___y_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___y_2836_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___y_2836_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___y_2836_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___y_2836_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_x_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2872_, v_x_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
return v_res_2879_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_box(0);
v___x_2881_ = l_Lean_interruptExceptionId;
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_){
_start:
{
lean_object* v_ks_2902_; lean_object* v_vs_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2935_; 
v_ks_2902_ = lean_ctor_get(v_x_2898_, 0);
v_vs_2903_ = lean_ctor_get(v_x_2898_, 1);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_x_2898_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2905_ = v_x_2898_;
v_isShared_2906_ = v_isSharedCheck_2935_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_vs_2903_);
lean_inc(v_ks_2902_);
lean_dec(v_x_2898_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2935_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = lean_array_get_size(v_ks_2902_);
v___x_2908_ = lean_nat_dec_lt(v_x_2899_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
lean_dec(v_x_2899_);
v___x_2909_ = lean_array_push(v_ks_2902_, v_x_2900_);
v___x_2910_ = lean_array_push(v_vs_2903_, v_x_2901_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v___x_2910_);
lean_ctor_set(v___x_2905_, 0, v___x_2909_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
else
{
lean_object* v_expr_2914_; uint64_t v_configKey_2915_; lean_object* v_k_x27_2916_; lean_object* v_expr_2917_; uint64_t v_configKey_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint8_t v___x_2923_; 
v_expr_2914_ = lean_ctor_get(v_x_2900_, 0);
v_configKey_2915_ = lean_ctor_get_uint64(v_x_2900_, sizeof(void*)*1);
v_k_x27_2916_ = lean_array_fget_borrowed(v_ks_2902_, v_x_2899_);
v_expr_2917_ = lean_ctor_get(v_k_x27_2916_, 0);
v_configKey_2918_ = lean_ctor_get_uint64(v_k_x27_2916_, sizeof(void*)*1);
v___x_2919_ = l_Lean_Expr_hash(v_expr_2914_);
v___x_2920_ = lean_uint64_mix_hash(v___x_2919_, v_configKey_2915_);
v___x_2921_ = l_Lean_Expr_hash(v_expr_2917_);
v___x_2922_ = lean_uint64_mix_hash(v___x_2921_, v_configKey_2918_);
v___x_2923_ = lean_uint64_dec_eq(v___x_2920_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2925_; 
if (v_isShared_2906_ == 0)
{
v___x_2925_ = v___x_2905_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_ks_2902_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_vs_2903_);
v___x_2925_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_x_2899_, v___x_2926_);
lean_dec(v_x_2899_);
v_x_2898_ = v___x_2925_;
v_x_2899_ = v___x_2927_;
goto _start;
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2930_ = lean_array_fset(v_ks_2902_, v_x_2899_, v_x_2900_);
v___x_2931_ = lean_array_fset(v_vs_2903_, v_x_2899_, v_x_2901_);
lean_dec(v_x_2899_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v___x_2931_);
lean_ctor_set(v___x_2905_, 0, v___x_2930_);
v___x_2933_ = v___x_2905_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2936_, lean_object* v_k_2937_, lean_object* v_v_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_n_2936_, v___x_2939_, v_k_2937_, v_v_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2941_, size_t v_x_2942_, size_t v_x_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
lean_object* v_es_2946_; size_t v___x_2947_; size_t v___x_2948_; lean_object* v_j_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v_es_2946_ = lean_ctor_get(v_x_2941_, 0);
v___x_2947_ = ((size_t)31ULL);
v___x_2948_ = lean_usize_land(v_x_2942_, v___x_2947_);
v_j_2949_ = lean_usize_to_nat(v___x_2948_);
v___x_2950_ = lean_array_get_size(v_es_2946_);
v___x_2951_ = lean_nat_dec_lt(v_j_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_dec(v_j_2949_);
lean_dec(v_x_2945_);
lean_dec_ref(v_x_2944_);
return v_x_2941_;
}
else
{
lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2998_; 
lean_inc_ref(v_es_2946_);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_x_2941_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v_x_2941_, 0);
lean_dec(v_unused_2999_);
v___x_2953_ = v_x_2941_;
v_isShared_2954_ = v_isSharedCheck_2998_;
goto v_resetjp_2952_;
}
else
{
lean_dec(v_x_2941_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2998_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_v_2955_; lean_object* v___x_2956_; lean_object* v_xs_x27_2957_; lean_object* v___y_2959_; 
v_v_2955_ = lean_array_fget(v_es_2946_, v_j_2949_);
v___x_2956_ = lean_box(0);
v_xs_x27_2957_ = lean_array_fset(v_es_2946_, v_j_2949_, v___x_2956_);
switch(lean_obj_tag(v_v_2955_))
{
case 0:
{
lean_object* v_key_2964_; lean_object* v_val_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2983_; 
v_key_2964_ = lean_ctor_get(v_v_2955_, 0);
v_val_2965_ = lean_ctor_get(v_v_2955_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_v_2955_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2967_ = v_v_2955_;
v_isShared_2968_ = v_isSharedCheck_2983_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_val_2965_);
lean_inc(v_key_2964_);
lean_dec(v_v_2955_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2983_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v_expr_2969_; uint64_t v_configKey_2970_; lean_object* v_expr_2971_; uint64_t v_configKey_2972_; uint64_t v___x_2973_; uint64_t v___x_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; uint8_t v___x_2977_; 
v_expr_2969_ = lean_ctor_get(v_x_2944_, 0);
v_configKey_2970_ = lean_ctor_get_uint64(v_x_2944_, sizeof(void*)*1);
v_expr_2971_ = lean_ctor_get(v_key_2964_, 0);
v_configKey_2972_ = lean_ctor_get_uint64(v_key_2964_, sizeof(void*)*1);
v___x_2973_ = l_Lean_Expr_hash(v_expr_2969_);
v___x_2974_ = lean_uint64_mix_hash(v___x_2973_, v_configKey_2970_);
v___x_2975_ = l_Lean_Expr_hash(v_expr_2971_);
v___x_2976_ = lean_uint64_mix_hash(v___x_2975_, v_configKey_2972_);
v___x_2977_ = lean_uint64_dec_eq(v___x_2974_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_del_object(v___x_2967_);
v___x_2978_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2964_, v_val_2965_, v_x_2944_, v_x_2945_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
v___y_2959_ = v___x_2979_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2981_; 
lean_dec(v_val_2965_);
lean_dec(v_key_2964_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v_x_2945_);
lean_ctor_set(v___x_2967_, 0, v_x_2944_);
v___x_2981_ = v___x_2967_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_x_2944_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_x_2945_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
v___y_2959_ = v___x_2981_;
goto v___jp_2958_;
}
}
}
}
case 1:
{
lean_object* v_node_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2996_; 
v_node_2984_ = lean_ctor_get(v_v_2955_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_v_2955_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2986_ = v_v_2955_;
v_isShared_2987_ = v_isSharedCheck_2996_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_node_2984_);
lean_dec(v_v_2955_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2996_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
size_t v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2988_ = ((size_t)5ULL);
v___x_2989_ = lean_usize_shift_right(v_x_2942_, v___x_2988_);
v___x_2990_ = ((size_t)1ULL);
v___x_2991_ = lean_usize_add(v_x_2943_, v___x_2990_);
v___x_2992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2984_, v___x_2989_, v___x_2991_, v_x_2944_, v_x_2945_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2992_);
v___x_2994_ = v___x_2986_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2959_ = v___x_2994_;
goto v___jp_2958_;
}
}
}
default: 
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_x_2944_);
lean_ctor_set(v___x_2997_, 1, v_x_2945_);
v___y_2959_ = v___x_2997_;
goto v___jp_2958_;
}
}
v___jp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = lean_array_fset(v_xs_x27_2957_, v_j_2949_, v___y_2959_);
lean_dec(v_j_2949_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2960_);
v___x_2962_ = v___x_2953_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
else
{
lean_object* v_ks_3000_; lean_object* v_vs_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3019_; 
v_ks_3000_ = lean_ctor_get(v_x_2941_, 0);
v_vs_3001_ = lean_ctor_get(v_x_2941_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_x_2941_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3003_ = v_x_2941_;
v_isShared_3004_ = v_isSharedCheck_3019_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_vs_3001_);
lean_inc(v_ks_3000_);
lean_dec(v_x_2941_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3019_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_ks_3000_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_vs_3001_);
v___x_3006_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v_newNode_3007_; size_t v___x_3008_; uint8_t v___x_3009_; 
v_newNode_3007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3006_, v_x_2944_, v_x_2945_);
v___x_3008_ = ((size_t)7ULL);
v___x_3009_ = lean_usize_dec_le(v___x_3008_, v_x_2943_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3007_);
v___x_3011_ = lean_unsigned_to_nat(4u);
v___x_3012_ = lean_nat_dec_lt(v___x_3010_, v___x_3011_);
lean_dec(v___x_3010_);
if (v___x_3012_ == 0)
{
lean_object* v_ks_3013_; lean_object* v_vs_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_ks_3013_ = lean_ctor_get(v_newNode_3007_, 0);
lean_inc_ref(v_ks_3013_);
v_vs_3014_ = lean_ctor_get(v_newNode_3007_, 1);
lean_inc_ref(v_vs_3014_);
lean_dec_ref(v_newNode_3007_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2943_, v_ks_3013_, v_vs_3014_, v___x_3015_, v___x_3016_);
lean_dec_ref(v_vs_3014_);
lean_dec_ref(v_ks_3013_);
return v___x_3017_;
}
else
{
return v_newNode_3007_;
}
}
else
{
return v_newNode_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3020_, lean_object* v_keys_3021_, lean_object* v_vals_3022_, lean_object* v_i_3023_, lean_object* v_entries_3024_){
_start:
{
lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = lean_array_get_size(v_keys_3021_);
v___x_3026_ = lean_nat_dec_lt(v_i_3023_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_dec(v_i_3023_);
return v_entries_3024_;
}
else
{
lean_object* v_k_3027_; lean_object* v_expr_3028_; uint64_t v_configKey_3029_; lean_object* v_v_3030_; uint64_t v___x_3031_; uint64_t v___x_3032_; size_t v_h_3033_; size_t v___x_3034_; lean_object* v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; size_t v___x_3038_; size_t v_h_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_k_3027_ = lean_array_fget_borrowed(v_keys_3021_, v_i_3023_);
v_expr_3028_ = lean_ctor_get(v_k_3027_, 0);
v_configKey_3029_ = lean_ctor_get_uint64(v_k_3027_, sizeof(void*)*1);
v_v_3030_ = lean_array_fget_borrowed(v_vals_3022_, v_i_3023_);
v___x_3031_ = l_Lean_Expr_hash(v_expr_3028_);
v___x_3032_ = lean_uint64_mix_hash(v___x_3031_, v_configKey_3029_);
v_h_3033_ = lean_uint64_to_usize(v___x_3032_);
v___x_3034_ = ((size_t)5ULL);
v___x_3035_ = lean_unsigned_to_nat(1u);
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_sub(v_depth_3020_, v___x_3036_);
v___x_3038_ = lean_usize_mul(v___x_3034_, v___x_3037_);
v_h_3039_ = lean_usize_shift_right(v_h_3033_, v___x_3038_);
v___x_3040_ = lean_nat_add(v_i_3023_, v___x_3035_);
lean_dec(v_i_3023_);
lean_inc(v_v_3030_);
lean_inc(v_k_3027_);
v___x_3041_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3024_, v_h_3039_, v_depth_3020_, v_k_3027_, v_v_3030_);
v_i_3023_ = v___x_3040_;
v_entries_3024_ = v___x_3041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3043_, lean_object* v_keys_3044_, lean_object* v_vals_3045_, lean_object* v_i_3046_, lean_object* v_entries_3047_){
_start:
{
size_t v_depth_boxed_3048_; lean_object* v_res_3049_; 
v_depth_boxed_3048_ = lean_unbox_usize(v_depth_3043_);
lean_dec(v_depth_3043_);
v_res_3049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3048_, v_keys_3044_, v_vals_3045_, v_i_3046_, v_entries_3047_);
lean_dec_ref(v_vals_3045_);
lean_dec_ref(v_keys_3044_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
size_t v_x_3752__boxed_3055_; size_t v_x_3753__boxed_3056_; lean_object* v_res_3057_; 
v_x_3752__boxed_3055_ = lean_unbox_usize(v_x_3051_);
lean_dec(v_x_3051_);
v_x_3753__boxed_3056_ = lean_unbox_usize(v_x_3052_);
lean_dec(v_x_3052_);
v_res_3057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3050_, v_x_3752__boxed_3055_, v_x_3753__boxed_3056_, v_x_3053_, v_x_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v_expr_3061_; uint64_t v_configKey_3062_; uint64_t v___x_3063_; uint64_t v___x_3064_; size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v_expr_3061_ = lean_ctor_get(v_x_3059_, 0);
v_configKey_3062_ = lean_ctor_get_uint64(v_x_3059_, sizeof(void*)*1);
v___x_3063_ = l_Lean_Expr_hash(v_expr_3061_);
v___x_3064_ = lean_uint64_mix_hash(v___x_3063_, v_configKey_3062_);
v___x_3065_ = lean_uint64_to_usize(v___x_3064_);
v___x_3066_ = ((size_t)1ULL);
v___x_3067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3058_, v___x_3065_, v___x_3066_, v_x_3059_, v_x_3060_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3068_, lean_object* v_vals_3069_, lean_object* v_i_3070_, lean_object* v_k_3071_){
_start:
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = lean_array_get_size(v_keys_3068_);
v___x_3073_ = lean_nat_dec_lt(v_i_3070_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
lean_dec(v_i_3070_);
v___x_3074_ = lean_box(0);
return v___x_3074_;
}
else
{
lean_object* v_expr_3075_; uint64_t v_configKey_3076_; lean_object* v_k_x27_3077_; lean_object* v_expr_3078_; uint64_t v_configKey_3079_; uint64_t v___x_3080_; uint64_t v___x_3081_; uint64_t v___x_3082_; uint64_t v___x_3083_; uint8_t v___x_3084_; 
v_expr_3075_ = lean_ctor_get(v_k_3071_, 0);
v_configKey_3076_ = lean_ctor_get_uint64(v_k_3071_, sizeof(void*)*1);
v_k_x27_3077_ = lean_array_fget_borrowed(v_keys_3068_, v_i_3070_);
v_expr_3078_ = lean_ctor_get(v_k_x27_3077_, 0);
v_configKey_3079_ = lean_ctor_get_uint64(v_k_x27_3077_, sizeof(void*)*1);
v___x_3080_ = l_Lean_Expr_hash(v_expr_3075_);
v___x_3081_ = lean_uint64_mix_hash(v___x_3080_, v_configKey_3076_);
v___x_3082_ = l_Lean_Expr_hash(v_expr_3078_);
v___x_3083_ = lean_uint64_mix_hash(v___x_3082_, v_configKey_3079_);
v___x_3084_ = lean_uint64_dec_eq(v___x_3081_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_unsigned_to_nat(1u);
v___x_3086_ = lean_nat_add(v_i_3070_, v___x_3085_);
lean_dec(v_i_3070_);
v_i_3070_ = v___x_3086_;
goto _start;
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_array_fget_borrowed(v_vals_3069_, v_i_3070_);
lean_dec(v_i_3070_);
lean_inc(v___x_3088_);
lean_inc(v_k_x27_3077_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v_k_x27_3077_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3091_, lean_object* v_vals_3092_, lean_object* v_i_3093_, lean_object* v_k_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3091_, v_vals_3092_, v_i_3093_, v_k_3094_);
lean_dec_ref(v_k_3094_);
lean_dec_ref(v_vals_3092_);
lean_dec_ref(v_keys_3091_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3096_, size_t v_x_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_es_3099_; lean_object* v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; lean_object* v_j_3103_; lean_object* v___x_3104_; 
v_es_3099_ = lean_ctor_get(v_x_3096_, 0);
v___x_3100_ = lean_box(2);
v___x_3101_ = ((size_t)31ULL);
v___x_3102_ = lean_usize_land(v_x_3097_, v___x_3101_);
v_j_3103_ = lean_usize_to_nat(v___x_3102_);
v___x_3104_ = lean_array_get_borrowed(v___x_3100_, v_es_3099_, v_j_3103_);
lean_dec(v_j_3103_);
switch(lean_obj_tag(v___x_3104_))
{
case 0:
{
lean_object* v_key_3105_; lean_object* v_val_3106_; lean_object* v_expr_3107_; uint64_t v_configKey_3108_; lean_object* v_expr_3109_; uint64_t v_configKey_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v___x_3113_; uint64_t v___x_3114_; uint8_t v___x_3115_; 
v_key_3105_ = lean_ctor_get(v___x_3104_, 0);
v_val_3106_ = lean_ctor_get(v___x_3104_, 1);
v_expr_3107_ = lean_ctor_get(v_x_3098_, 0);
v_configKey_3108_ = lean_ctor_get_uint64(v_x_3098_, sizeof(void*)*1);
v_expr_3109_ = lean_ctor_get(v_key_3105_, 0);
v_configKey_3110_ = lean_ctor_get_uint64(v_key_3105_, sizeof(void*)*1);
v___x_3111_ = l_Lean_Expr_hash(v_expr_3107_);
v___x_3112_ = lean_uint64_mix_hash(v___x_3111_, v_configKey_3108_);
v___x_3113_ = l_Lean_Expr_hash(v_expr_3109_);
v___x_3114_ = lean_uint64_mix_hash(v___x_3113_, v_configKey_3110_);
v___x_3115_ = lean_uint64_dec_eq(v___x_3112_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_inc(v_val_3106_);
lean_inc(v_key_3105_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_key_3105_);
lean_ctor_set(v___x_3117_, 1, v_val_3106_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
case 1:
{
lean_object* v_node_3119_; size_t v___x_3120_; size_t v___x_3121_; 
v_node_3119_ = lean_ctor_get(v___x_3104_, 0);
v___x_3120_ = ((size_t)5ULL);
v___x_3121_ = lean_usize_shift_right(v_x_3097_, v___x_3120_);
v_x_3096_ = v_node_3119_;
v_x_3097_ = v___x_3121_;
goto _start;
}
default: 
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
}
}
else
{
lean_object* v_ks_3124_; lean_object* v_vs_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_ks_3124_ = lean_ctor_get(v_x_3096_, 0);
v_vs_3125_ = lean_ctor_get(v_x_3096_, 1);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3124_, v_vs_3125_, v___x_3126_, v_x_3098_);
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3128_, lean_object* v_x_3129_, lean_object* v_x_3130_){
_start:
{
size_t v_x_3978__boxed_3131_; lean_object* v_res_3132_; 
v_x_3978__boxed_3131_ = lean_unbox_usize(v_x_3129_);
lean_dec(v_x_3129_);
v_res_3132_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3128_, v_x_3978__boxed_3131_, v_x_3130_);
lean_dec_ref(v_x_3130_);
lean_dec_ref(v_x_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v_expr_3135_; uint64_t v_configKey_3136_; uint64_t v___x_3137_; uint64_t v___x_3138_; size_t v___x_3139_; lean_object* v___x_3140_; 
v_expr_3135_ = lean_ctor_get(v_x_3134_, 0);
v_configKey_3136_ = lean_ctor_get_uint64(v_x_3134_, sizeof(void*)*1);
v___x_3137_ = l_Lean_Expr_hash(v_expr_3135_);
v___x_3138_ = lean_uint64_mix_hash(v___x_3137_, v_configKey_3136_);
v___x_3139_ = lean_uint64_to_usize(v___x_3138_);
v___x_3140_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3133_, v___x_3139_, v_x_3134_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3141_, lean_object* v_x_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3141_, v_x_3142_);
lean_dec_ref(v_x_3142_);
lean_dec_ref(v_x_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(lean_object* v_xs_3144_, lean_object* v_v_3145_, lean_object* v_i_3146_){
_start:
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = lean_array_get_size(v_xs_3144_);
v___x_3148_ = lean_nat_dec_lt(v_i_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; 
lean_dec(v_i_3146_);
v___x_3149_ = lean_box(0);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v_expr_3151_; uint64_t v_configKey_3152_; lean_object* v_expr_3153_; uint64_t v_configKey_3154_; uint64_t v___x_3155_; uint64_t v___x_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; uint8_t v___x_3159_; 
v___x_3150_ = lean_array_fget_borrowed(v_xs_3144_, v_i_3146_);
v_expr_3151_ = lean_ctor_get(v___x_3150_, 0);
v_configKey_3152_ = lean_ctor_get_uint64(v___x_3150_, sizeof(void*)*1);
v_expr_3153_ = lean_ctor_get(v_v_3145_, 0);
v_configKey_3154_ = lean_ctor_get_uint64(v_v_3145_, sizeof(void*)*1);
v___x_3155_ = l_Lean_Expr_hash(v_expr_3151_);
v___x_3156_ = lean_uint64_mix_hash(v___x_3155_, v_configKey_3152_);
v___x_3157_ = l_Lean_Expr_hash(v_expr_3153_);
v___x_3158_ = lean_uint64_mix_hash(v___x_3157_, v_configKey_3154_);
v___x_3159_ = lean_uint64_dec_eq(v___x_3156_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_nat_add(v_i_3146_, v___x_3160_);
lean_dec(v_i_3146_);
v_i_3146_ = v___x_3161_;
goto _start;
}
else
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_i_3146_);
return v___x_3163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11___boxed(lean_object* v_xs_3164_, lean_object* v_v_3165_, lean_object* v_i_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3164_, v_v_3165_, v_i_3166_);
lean_dec_ref(v_v_3165_);
lean_dec_ref(v_xs_3164_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(lean_object* v_xs_3168_, lean_object* v_v_3169_){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3168_, v_v_3169_, v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9___boxed(lean_object* v_xs_3172_, lean_object* v_v_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_xs_3172_, v_v_3173_);
lean_dec_ref(v_v_3173_);
lean_dec_ref(v_xs_3172_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(lean_object* v_x_3175_, size_t v_x_3176_, lean_object* v_x_3177_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 0)
{
lean_object* v_es_3178_; lean_object* v___x_3179_; size_t v___x_3180_; size_t v___x_3181_; lean_object* v_j_3182_; lean_object* v_entry_3183_; 
v_es_3178_ = lean_ctor_get(v_x_3175_, 0);
v___x_3179_ = lean_box(2);
v___x_3180_ = ((size_t)31ULL);
v___x_3181_ = lean_usize_land(v_x_3176_, v___x_3180_);
v_j_3182_ = lean_usize_to_nat(v___x_3181_);
v_entry_3183_ = lean_array_get(v___x_3179_, v_es_3178_, v_j_3182_);
switch(lean_obj_tag(v_entry_3183_))
{
case 0:
{
lean_object* v_key_3184_; lean_object* v_expr_3185_; uint64_t v_configKey_3186_; lean_object* v_expr_3187_; uint64_t v_configKey_3188_; uint64_t v___x_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v___x_3192_; uint8_t v___x_3193_; 
v_key_3184_ = lean_ctor_get(v_entry_3183_, 0);
lean_inc(v_key_3184_);
lean_dec_ref_known(v_entry_3183_, 2);
v_expr_3185_ = lean_ctor_get(v_x_3177_, 0);
v_configKey_3186_ = lean_ctor_get_uint64(v_x_3177_, sizeof(void*)*1);
v_expr_3187_ = lean_ctor_get(v_key_3184_, 0);
lean_inc_ref(v_expr_3187_);
v_configKey_3188_ = lean_ctor_get_uint64(v_key_3184_, sizeof(void*)*1);
lean_dec(v_key_3184_);
v___x_3189_ = l_Lean_Expr_hash(v_expr_3185_);
v___x_3190_ = lean_uint64_mix_hash(v___x_3189_, v_configKey_3186_);
v___x_3191_ = l_Lean_Expr_hash(v_expr_3187_);
lean_dec_ref(v_expr_3187_);
v___x_3192_ = lean_uint64_mix_hash(v___x_3191_, v_configKey_3188_);
v___x_3193_ = lean_uint64_dec_eq(v___x_3190_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_dec(v_j_3182_);
return v_x_3175_;
}
else
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3201_; 
lean_inc_ref(v_es_3178_);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v_x_3175_, 0);
lean_dec(v_unused_3202_);
v___x_3195_ = v_x_3175_;
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v_x_3175_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3197_ = lean_array_set(v_es_3178_, v_j_3182_, v___x_3179_);
lean_dec(v_j_3182_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
case 1:
{
lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3237_; 
lean_inc_ref(v_es_3178_);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v_x_3175_, 0);
lean_dec(v_unused_3238_);
v___x_3204_ = v_x_3175_;
v_isShared_3205_ = v_isSharedCheck_3237_;
goto v_resetjp_3203_;
}
else
{
lean_dec(v_x_3175_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3237_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_node_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3236_; 
v_node_3206_ = lean_ctor_get(v_entry_3183_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_entry_3183_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3208_ = v_entry_3183_;
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_node_3206_);
lean_dec(v_entry_3183_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
size_t v___x_3210_; lean_object* v_entries_3211_; size_t v___x_3212_; lean_object* v_newNode_3213_; lean_object* v___x_3214_; 
v___x_3210_ = ((size_t)5ULL);
v_entries_3211_ = lean_array_set(v_es_3178_, v_j_3182_, v___x_3179_);
v___x_3212_ = lean_usize_shift_right(v_x_3176_, v___x_3210_);
v_newNode_3213_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_node_3206_, v___x_3212_, v_x_3177_);
lean_inc_ref(v_newNode_3213_);
v___x_3214_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v___x_3216_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v_newNode_3213_);
v___x_3216_ = v___x_3208_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_newNode_3213_);
v___x_3216_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_array_set(v_entries_3211_, v_j_3182_, v___x_3216_);
lean_dec(v_j_3182_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3217_);
v___x_3219_ = v___x_3204_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
lean_object* v_val_3222_; lean_object* v_fst_3223_; lean_object* v_snd_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_newNode_3213_);
lean_del_object(v___x_3208_);
v_val_3222_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v___x_3214_, 1);
v_fst_3223_ = lean_ctor_get(v_val_3222_, 0);
v_snd_3224_ = lean_ctor_get(v_val_3222_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_val_3222_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3226_ = v_val_3222_;
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snd_3224_);
lean_inc(v_fst_3223_);
lean_dec(v_val_3222_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_fst_3223_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_snd_3224_);
v___x_3229_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_array_set(v_entries_3211_, v_j_3182_, v___x_3229_);
lean_dec(v_j_3182_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3230_);
v___x_3232_ = v___x_3204_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_3182_);
return v_x_3175_;
}
}
}
else
{
lean_object* v_ks_3239_; lean_object* v_vs_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3254_; 
v_ks_3239_ = lean_ctor_get(v_x_3175_, 0);
v_vs_3240_ = lean_ctor_get(v_x_3175_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3242_ = v_x_3175_;
v_isShared_3243_ = v_isSharedCheck_3254_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_vs_3240_);
lean_inc(v_ks_3239_);
lean_dec(v_x_3175_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3254_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_ks_3239_, v_x_3177_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3246_; 
if (v_isShared_3243_ == 0)
{
v___x_3246_ = v___x_3242_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_ks_3239_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_vs_3240_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
else
{
lean_object* v_val_3248_; lean_object* v_keys_x27_3249_; lean_object* v_vals_x27_3250_; lean_object* v___x_3252_; 
v_val_3248_ = lean_ctor_get(v___x_3244_, 0);
lean_inc_n(v_val_3248_, 2);
lean_dec_ref_known(v___x_3244_, 1);
v_keys_x27_3249_ = l_Array_eraseIdx___redArg(v_ks_3239_, v_val_3248_);
v_vals_x27_3250_ = l_Array_eraseIdx___redArg(v_vs_3240_, v_val_3248_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v_vals_x27_3250_);
lean_ctor_set(v___x_3242_, 0, v_keys_x27_3249_);
v___x_3252_ = v___x_3242_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_keys_x27_3249_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_vals_x27_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg___boxed(lean_object* v_x_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
size_t v_x_4099__boxed_3258_; lean_object* v_res_3259_; 
v_x_4099__boxed_3258_ = lean_unbox_usize(v_x_3256_);
lean_dec(v_x_3256_);
v_res_3259_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3255_, v_x_4099__boxed_3258_, v_x_3257_);
lean_dec_ref(v_x_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_expr_3262_; uint64_t v_configKey_3263_; uint64_t v___x_3264_; uint64_t v___x_3265_; size_t v_h_3266_; lean_object* v___x_3267_; 
v_expr_3262_ = lean_ctor_get(v_x_3261_, 0);
v_configKey_3263_ = lean_ctor_get_uint64(v_x_3261_, sizeof(void*)*1);
v___x_3264_ = l_Lean_Expr_hash(v_expr_3262_);
v___x_3265_ = lean_uint64_mix_hash(v___x_3264_, v_configKey_3263_);
v_h_3266_ = lean_uint64_to_usize(v___x_3265_);
v___x_3267_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3260_, v_h_3266_, v_x_3261_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg___boxed(lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3268_, v_x_3269_);
lean_dec_ref(v_x_3269_);
return v_res_3270_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3273_ = l_Lean_stringToMessageData(v___x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
switch(lean_obj_tag(v_e_3274_))
{
case 0:
{
lean_object* v_deBruijnIndex_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_deBruijnIndex_3312_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_deBruijnIndex_3312_);
lean_dec_ref_known(v_e_3274_, 1);
v___x_3313_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3314_ = l_Lean_mkBVar(v_deBruijnIndex_3312_);
v___x_3315_ = l_Lean_MessageData_ofExpr(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3313_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3316_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3317_;
}
case 1:
{
lean_object* v_fvarId_3318_; lean_object* v___x_3319_; 
v_fvarId_3318_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_fvarId_3318_);
lean_dec_ref_known(v_e_3274_, 1);
v___x_3319_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3318_, v_a_3275_, v_a_3277_, v_a_3278_);
return v___x_3319_;
}
case 2:
{
lean_object* v_mvarId_3320_; lean_object* v___x_3321_; 
v_mvarId_3320_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_mvarId_3320_);
lean_dec_ref_known(v_e_3274_, 1);
v___x_3321_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3320_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3321_;
}
case 3:
{
lean_object* v_u_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_u_3322_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_u_3322_);
lean_dec_ref_known(v_e_3274_, 1);
v___x_3323_ = l_Lean_Level_succ___override(v_u_3322_);
v___x_3324_ = l_Lean_mkSort(v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
case 4:
{
lean_object* v_declName_3326_; lean_object* v_us_3327_; 
v_declName_3326_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_declName_3326_);
v_us_3327_ = lean_ctor_get(v_e_3274_, 1);
lean_inc(v_us_3327_);
if (lean_obj_tag(v_us_3327_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref_known(v_e_3274_, 2);
v___x_3344_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3326_, v_us_3327_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3344_;
}
else
{
uint8_t v_cacheInferType_3345_; 
v_cacheInferType_3345_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3345_ == 0)
{
lean_dec_ref_known(v_e_3274_, 2);
goto v___jp_3328_;
}
else
{
uint8_t v___x_3346_; 
v___x_3346_ = l_Lean_Expr_hasMVar(v_e_3274_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3453_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3453_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3453_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3407_; lean_object* v_cache_3408_; lean_object* v_inferType_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_st_ref_get(v_a_3276_);
v_cache_3408_ = lean_ctor_get(v___x_3407_, 1);
lean_inc_ref(v_cache_3408_);
lean_dec(v___x_3407_);
v_inferType_3409_ = lean_ctor_get(v_cache_3408_, 0);
lean_inc_ref(v_inferType_3409_);
lean_dec_ref(v_cache_3408_);
v___x_3410_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3409_, v_a_3348_);
if (lean_obj_tag(v___x_3410_) == 1)
{
lean_object* v_val_3411_; lean_object* v_fst_3412_; lean_object* v_snd_3413_; lean_object* v_expr_3414_; uint64_t v_configKey_3415_; lean_object* v_expr_3416_; uint64_t v_configKey_3417_; uint8_t v___x_3418_; 
v_val_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_val_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v_fst_3412_ = lean_ctor_get(v_val_3411_, 0);
lean_inc(v_fst_3412_);
v_snd_3413_ = lean_ctor_get(v_val_3411_, 1);
lean_inc(v_snd_3413_);
lean_dec(v_val_3411_);
v_expr_3414_ = lean_ctor_get(v_a_3348_, 0);
v_configKey_3415_ = lean_ctor_get_uint64(v_a_3348_, sizeof(void*)*1);
v_expr_3416_ = lean_ctor_get(v_fst_3412_, 0);
lean_inc_ref(v_expr_3416_);
v_configKey_3417_ = lean_ctor_get_uint64(v_fst_3412_, sizeof(void*)*1);
lean_dec(v_fst_3412_);
v___x_3418_ = lean_uint64_dec_eq(v_configKey_3415_, v_configKey_3417_);
if (v___x_3418_ == 0)
{
lean_dec_ref(v_expr_3416_);
lean_dec(v_snd_3413_);
lean_dec_ref(v_inferType_3409_);
lean_del_object(v___x_3350_);
goto v___jp_3393_;
}
else
{
size_t v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = ((size_t)64ULL);
v___x_3420_ = lean_expr_equal_budgeted(v_expr_3414_, v_expr_3416_, v___x_3419_);
lean_dec_ref(v_expr_3416_);
switch(v___x_3420_)
{
case 0:
{
lean_dec(v_snd_3413_);
lean_dec_ref(v_inferType_3409_);
lean_del_object(v___x_3350_);
goto v___jp_3393_;
}
case 1:
{
lean_object* v___x_3422_; 
lean_dec_ref(v_inferType_3409_);
lean_dec(v_a_3348_);
lean_dec(v_us_3327_);
lean_dec(v_declName_3326_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_snd_3413_);
v___x_3422_ = v___x_3350_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_snd_3413_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
default: 
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v_cache_3426_; lean_object* v_mctx_3427_; lean_object* v_zetaDeltaFVarIds_3428_; lean_object* v_postponed_3429_; lean_object* v_diag_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_snd_3413_);
lean_del_object(v___x_3350_);
v___x_3424_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3409_, v_a_3348_);
v___x_3425_ = lean_st_ref_take(v_a_3276_);
v_cache_3426_ = lean_ctor_get(v___x_3425_, 1);
v_mctx_3427_ = lean_ctor_get(v___x_3425_, 0);
v_zetaDeltaFVarIds_3428_ = lean_ctor_get(v___x_3425_, 2);
v_postponed_3429_ = lean_ctor_get(v___x_3425_, 3);
v_diag_3430_ = lean_ctor_get(v___x_3425_, 4);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3432_ = v___x_3425_;
v_isShared_3433_ = v_isSharedCheck_3452_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_diag_3430_);
lean_inc(v_postponed_3429_);
lean_inc(v_zetaDeltaFVarIds_3428_);
lean_inc(v_cache_3426_);
lean_inc(v_mctx_3427_);
lean_dec(v___x_3425_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3452_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_funInfo_3434_; lean_object* v_synthInstance_3435_; lean_object* v_whnf_3436_; lean_object* v_defEqTrans_3437_; lean_object* v_defEqPerm_3438_; lean_object* v_isUnitLike_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3450_; 
v_funInfo_3434_ = lean_ctor_get(v_cache_3426_, 1);
v_synthInstance_3435_ = lean_ctor_get(v_cache_3426_, 2);
v_whnf_3436_ = lean_ctor_get(v_cache_3426_, 3);
v_defEqTrans_3437_ = lean_ctor_get(v_cache_3426_, 4);
v_defEqPerm_3438_ = lean_ctor_get(v_cache_3426_, 5);
v_isUnitLike_3439_ = lean_ctor_get(v_cache_3426_, 6);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_cache_3426_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v_cache_3426_, 0);
lean_dec(v_unused_3451_);
v___x_3441_ = v_cache_3426_;
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_isUnitLike_3439_);
lean_inc(v_defEqPerm_3438_);
lean_inc(v_defEqTrans_3437_);
lean_inc(v_whnf_3436_);
lean_inc(v_synthInstance_3435_);
lean_inc(v_funInfo_3434_);
lean_dec(v_cache_3426_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3424_);
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_funInfo_3434_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_synthInstance_3435_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_whnf_3436_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_defEqTrans_3437_);
lean_ctor_set(v_reuseFailAlloc_3449_, 5, v_defEqPerm_3438_);
lean_ctor_set(v_reuseFailAlloc_3449_, 6, v_isUnitLike_3439_);
v___x_3444_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3444_);
v___x_3446_ = v___x_3432_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_mctx_3427_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_zetaDeltaFVarIds_3428_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_postponed_3429_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_diag_3430_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_st_ref_put(v_a_3276_, v___x_3446_);
goto v___jp_3393_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3410_);
lean_dec_ref(v_inferType_3409_);
lean_del_object(v___x_3350_);
goto v___jp_3393_;
}
v___jp_3352_:
{
lean_object* v___x_3353_; 
v___x_3353_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3326_, v_us_3327_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; uint8_t v___x_3355_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v___x_3355_ = l_Lean_Expr_hasMVar(v_a_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3391_; 
lean_inc(v_a_3354_);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v___x_3353_, 0);
lean_dec(v_unused_3392_);
v___x_3357_ = v___x_3353_;
v_isShared_3358_ = v_isSharedCheck_3391_;
goto v_resetjp_3356_;
}
else
{
lean_dec(v___x_3353_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3391_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v_cache_3360_; lean_object* v_mctx_3361_; lean_object* v_zetaDeltaFVarIds_3362_; lean_object* v_postponed_3363_; lean_object* v_diag_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3390_; 
v___x_3359_ = lean_st_ref_take(v_a_3276_);
v_cache_3360_ = lean_ctor_get(v___x_3359_, 1);
v_mctx_3361_ = lean_ctor_get(v___x_3359_, 0);
v_zetaDeltaFVarIds_3362_ = lean_ctor_get(v___x_3359_, 2);
v_postponed_3363_ = lean_ctor_get(v___x_3359_, 3);
v_diag_3364_ = lean_ctor_get(v___x_3359_, 4);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3366_ = v___x_3359_;
v_isShared_3367_ = v_isSharedCheck_3390_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_diag_3364_);
lean_inc(v_postponed_3363_);
lean_inc(v_zetaDeltaFVarIds_3362_);
lean_inc(v_cache_3360_);
lean_inc(v_mctx_3361_);
lean_dec(v___x_3359_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3390_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_inferType_3368_; lean_object* v_funInfo_3369_; lean_object* v_synthInstance_3370_; lean_object* v_whnf_3371_; lean_object* v_defEqTrans_3372_; lean_object* v_defEqPerm_3373_; lean_object* v_isUnitLike_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3389_; 
v_inferType_3368_ = lean_ctor_get(v_cache_3360_, 0);
v_funInfo_3369_ = lean_ctor_get(v_cache_3360_, 1);
v_synthInstance_3370_ = lean_ctor_get(v_cache_3360_, 2);
v_whnf_3371_ = lean_ctor_get(v_cache_3360_, 3);
v_defEqTrans_3372_ = lean_ctor_get(v_cache_3360_, 4);
v_defEqPerm_3373_ = lean_ctor_get(v_cache_3360_, 5);
v_isUnitLike_3374_ = lean_ctor_get(v_cache_3360_, 6);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_cache_3360_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3376_ = v_cache_3360_;
v_isShared_3377_ = v_isSharedCheck_3389_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_isUnitLike_3374_);
lean_inc(v_defEqPerm_3373_);
lean_inc(v_defEqTrans_3372_);
lean_inc(v_whnf_3371_);
lean_inc(v_synthInstance_3370_);
lean_inc(v_funInfo_3369_);
lean_inc(v_inferType_3368_);
lean_dec(v_cache_3360_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3389_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_inc(v_a_3354_);
v___x_3378_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3368_, v_a_3348_, v_a_3354_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_funInfo_3369_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_synthInstance_3370_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_whnf_3371_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v_defEqTrans_3372_);
lean_ctor_set(v_reuseFailAlloc_3388_, 5, v_defEqPerm_3373_);
lean_ctor_set(v_reuseFailAlloc_3388_, 6, v_isUnitLike_3374_);
v___x_3380_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3382_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3380_);
v___x_3382_ = v___x_3366_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_mctx_3361_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3387_, 2, v_zetaDeltaFVarIds_3362_);
lean_ctor_set(v_reuseFailAlloc_3387_, 3, v_postponed_3363_);
lean_ctor_set(v_reuseFailAlloc_3387_, 4, v_diag_3364_);
v___x_3382_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_st_ref_put(v_a_3276_, v___x_3382_);
if (v_isShared_3358_ == 0)
{
v___x_3385_ = v___x_3357_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3354_);
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
}
}
}
else
{
lean_dec(v_a_3348_);
return v___x_3353_;
}
}
else
{
lean_dec(v_a_3348_);
return v___x_3353_;
}
}
v___jp_3393_:
{
lean_object* v_toCold_3394_; lean_object* v_cancelTk_x3f_3395_; 
v_toCold_3394_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3395_ = lean_ctor_get(v_toCold_3394_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3395_) == 1)
{
lean_object* v_val_3396_; uint8_t v___x_3397_; 
v_val_3396_ = lean_ctor_get(v_cancelTk_x3f_3395_, 0);
v___x_3397_ = l_IO_CancelToken_isSet(v_val_3396_);
if (v___x_3397_ == 0)
{
goto v___jp_3352_;
}
else
{
lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3348_);
lean_dec(v_us_3327_);
lean_dec(v_declName_3326_);
v___x_3398_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
goto v___jp_3352_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v_us_3327_);
lean_dec(v_declName_3326_);
v_a_3454_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3347_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3347_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3274_, 2);
goto v___jp_3328_;
}
}
}
v___jp_3328_:
{
lean_object* v_toCold_3329_; lean_object* v_cancelTk_x3f_3330_; 
v_toCold_3329_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3330_ = lean_ctor_get(v_toCold_3329_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3330_) == 1)
{
lean_object* v_val_3331_; uint8_t v___x_3332_; 
v_val_3331_ = lean_ctor_get(v_cancelTk_x3f_3330_, 0);
v___x_3332_ = l_IO_CancelToken_isSet(v_val_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3326_, v_us_3327_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_us_3327_);
lean_dec(v_declName_3326_);
v___x_3334_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3326_, v_us_3327_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3343_;
}
}
}
case 5:
{
lean_object* v_fn_3462_; uint8_t v_cacheInferType_3463_; lean_object* v_nargs_3464_; lean_object* v___x_3465_; lean_object* v_dummy_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_fn_3462_ = lean_ctor_get(v_e_3274_, 0);
v_cacheInferType_3463_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*7 + 3);
v_nargs_3464_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
v___x_3465_ = l_Lean_Expr_getAppFn(v_fn_3462_);
v_dummy_3466_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3464_);
v___x_3467_ = lean_mk_array(v_nargs_3464_, v_dummy_3466_);
v___x_3468_ = lean_unsigned_to_nat(1u);
v___x_3469_ = lean_nat_sub(v_nargs_3464_, v___x_3468_);
lean_dec(v_nargs_3464_);
lean_inc_ref(v_e_3274_);
v___x_3470_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3274_, v___x_3467_, v___x_3469_);
if (v_cacheInferType_3463_ == 0)
{
lean_dec_ref_known(v_e_3274_, 2);
goto v___jp_3471_;
}
else
{
uint8_t v___x_3487_; 
v___x_3487_ = l_Lean_Expr_hasMVar(v_e_3274_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3594_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3594_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3594_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3548_; lean_object* v_cache_3549_; lean_object* v_inferType_3550_; lean_object* v___x_3551_; 
v___x_3548_ = lean_st_ref_get(v_a_3276_);
v_cache_3549_ = lean_ctor_get(v___x_3548_, 1);
lean_inc_ref(v_cache_3549_);
lean_dec(v___x_3548_);
v_inferType_3550_ = lean_ctor_get(v_cache_3549_, 0);
lean_inc_ref(v_inferType_3550_);
lean_dec_ref(v_cache_3549_);
v___x_3551_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3550_, v_a_3489_);
if (lean_obj_tag(v___x_3551_) == 1)
{
lean_object* v_val_3552_; lean_object* v_fst_3553_; lean_object* v_snd_3554_; lean_object* v_expr_3555_; uint64_t v_configKey_3556_; lean_object* v_expr_3557_; uint64_t v_configKey_3558_; uint8_t v___x_3559_; 
v_val_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_val_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_fst_3553_ = lean_ctor_get(v_val_3552_, 0);
lean_inc(v_fst_3553_);
v_snd_3554_ = lean_ctor_get(v_val_3552_, 1);
lean_inc(v_snd_3554_);
lean_dec(v_val_3552_);
v_expr_3555_ = lean_ctor_get(v_a_3489_, 0);
v_configKey_3556_ = lean_ctor_get_uint64(v_a_3489_, sizeof(void*)*1);
v_expr_3557_ = lean_ctor_get(v_fst_3553_, 0);
lean_inc_ref(v_expr_3557_);
v_configKey_3558_ = lean_ctor_get_uint64(v_fst_3553_, sizeof(void*)*1);
lean_dec(v_fst_3553_);
v___x_3559_ = lean_uint64_dec_eq(v_configKey_3556_, v_configKey_3558_);
if (v___x_3559_ == 0)
{
lean_dec_ref(v_expr_3557_);
lean_dec(v_snd_3554_);
lean_dec_ref(v_inferType_3550_);
lean_del_object(v___x_3491_);
goto v___jp_3534_;
}
else
{
size_t v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = ((size_t)64ULL);
v___x_3561_ = lean_expr_equal_budgeted(v_expr_3555_, v_expr_3557_, v___x_3560_);
lean_dec_ref(v_expr_3557_);
switch(v___x_3561_)
{
case 0:
{
lean_dec(v_snd_3554_);
lean_dec_ref(v_inferType_3550_);
lean_del_object(v___x_3491_);
goto v___jp_3534_;
}
case 1:
{
lean_object* v___x_3563_; 
lean_dec_ref(v_inferType_3550_);
lean_dec(v_a_3489_);
lean_dec_ref(v___x_3470_);
lean_dec_ref(v___x_3465_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v_snd_3554_);
v___x_3563_ = v___x_3491_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_snd_3554_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
default: 
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_cache_3567_; lean_object* v_mctx_3568_; lean_object* v_zetaDeltaFVarIds_3569_; lean_object* v_postponed_3570_; lean_object* v_diag_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_snd_3554_);
lean_del_object(v___x_3491_);
v___x_3565_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3550_, v_a_3489_);
v___x_3566_ = lean_st_ref_take(v_a_3276_);
v_cache_3567_ = lean_ctor_get(v___x_3566_, 1);
v_mctx_3568_ = lean_ctor_get(v___x_3566_, 0);
v_zetaDeltaFVarIds_3569_ = lean_ctor_get(v___x_3566_, 2);
v_postponed_3570_ = lean_ctor_get(v___x_3566_, 3);
v_diag_3571_ = lean_ctor_get(v___x_3566_, 4);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3573_ = v___x_3566_;
v_isShared_3574_ = v_isSharedCheck_3593_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_diag_3571_);
lean_inc(v_postponed_3570_);
lean_inc(v_zetaDeltaFVarIds_3569_);
lean_inc(v_cache_3567_);
lean_inc(v_mctx_3568_);
lean_dec(v___x_3566_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3593_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v_funInfo_3575_; lean_object* v_synthInstance_3576_; lean_object* v_whnf_3577_; lean_object* v_defEqTrans_3578_; lean_object* v_defEqPerm_3579_; lean_object* v_isUnitLike_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3591_; 
v_funInfo_3575_ = lean_ctor_get(v_cache_3567_, 1);
v_synthInstance_3576_ = lean_ctor_get(v_cache_3567_, 2);
v_whnf_3577_ = lean_ctor_get(v_cache_3567_, 3);
v_defEqTrans_3578_ = lean_ctor_get(v_cache_3567_, 4);
v_defEqPerm_3579_ = lean_ctor_get(v_cache_3567_, 5);
v_isUnitLike_3580_ = lean_ctor_get(v_cache_3567_, 6);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_cache_3567_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v_cache_3567_, 0);
lean_dec(v_unused_3592_);
v___x_3582_ = v_cache_3567_;
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_isUnitLike_3580_);
lean_inc(v_defEqPerm_3579_);
lean_inc(v_defEqTrans_3578_);
lean_inc(v_whnf_3577_);
lean_inc(v_synthInstance_3576_);
lean_inc(v_funInfo_3575_);
lean_dec(v_cache_3567_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3591_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3565_);
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_funInfo_3575_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_synthInstance_3576_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_whnf_3577_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_defEqTrans_3578_);
lean_ctor_set(v_reuseFailAlloc_3590_, 5, v_defEqPerm_3579_);
lean_ctor_set(v_reuseFailAlloc_3590_, 6, v_isUnitLike_3580_);
v___x_3585_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3585_);
v___x_3587_ = v___x_3573_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_mctx_3568_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_zetaDeltaFVarIds_3569_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v_postponed_3570_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_diag_3571_);
v___x_3587_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_st_ref_put(v_a_3276_, v___x_3587_);
goto v___jp_3534_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3551_);
lean_dec_ref(v_inferType_3550_);
lean_del_object(v___x_3491_);
goto v___jp_3534_;
}
v___jp_3493_:
{
lean_object* v___x_3494_; 
v___x_3494_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3465_, v___x_3470_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec_ref(v___x_3470_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; uint8_t v___x_3496_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v___x_3496_ = l_Lean_Expr_hasMVar(v_a_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3532_; 
lean_inc(v_a_3495_);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3494_, 0);
lean_dec(v_unused_3533_);
v___x_3498_ = v___x_3494_;
v_isShared_3499_ = v_isSharedCheck_3532_;
goto v_resetjp_3497_;
}
else
{
lean_dec(v___x_3494_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3532_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v_cache_3501_; lean_object* v_mctx_3502_; lean_object* v_zetaDeltaFVarIds_3503_; lean_object* v_postponed_3504_; lean_object* v_diag_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3531_; 
v___x_3500_ = lean_st_ref_take(v_a_3276_);
v_cache_3501_ = lean_ctor_get(v___x_3500_, 1);
v_mctx_3502_ = lean_ctor_get(v___x_3500_, 0);
v_zetaDeltaFVarIds_3503_ = lean_ctor_get(v___x_3500_, 2);
v_postponed_3504_ = lean_ctor_get(v___x_3500_, 3);
v_diag_3505_ = lean_ctor_get(v___x_3500_, 4);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3507_ = v___x_3500_;
v_isShared_3508_ = v_isSharedCheck_3531_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_diag_3505_);
lean_inc(v_postponed_3504_);
lean_inc(v_zetaDeltaFVarIds_3503_);
lean_inc(v_cache_3501_);
lean_inc(v_mctx_3502_);
lean_dec(v___x_3500_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3531_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v_inferType_3509_; lean_object* v_funInfo_3510_; lean_object* v_synthInstance_3511_; lean_object* v_whnf_3512_; lean_object* v_defEqTrans_3513_; lean_object* v_defEqPerm_3514_; lean_object* v_isUnitLike_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3530_; 
v_inferType_3509_ = lean_ctor_get(v_cache_3501_, 0);
v_funInfo_3510_ = lean_ctor_get(v_cache_3501_, 1);
v_synthInstance_3511_ = lean_ctor_get(v_cache_3501_, 2);
v_whnf_3512_ = lean_ctor_get(v_cache_3501_, 3);
v_defEqTrans_3513_ = lean_ctor_get(v_cache_3501_, 4);
v_defEqPerm_3514_ = lean_ctor_get(v_cache_3501_, 5);
v_isUnitLike_3515_ = lean_ctor_get(v_cache_3501_, 6);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_cache_3501_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3517_ = v_cache_3501_;
v_isShared_3518_ = v_isSharedCheck_3530_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_isUnitLike_3515_);
lean_inc(v_defEqPerm_3514_);
lean_inc(v_defEqTrans_3513_);
lean_inc(v_whnf_3512_);
lean_inc(v_synthInstance_3511_);
lean_inc(v_funInfo_3510_);
lean_inc(v_inferType_3509_);
lean_dec(v_cache_3501_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3530_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
lean_inc(v_a_3495_);
v___x_3519_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3509_, v_a_3489_, v_a_3495_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3519_);
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_funInfo_3510_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_synthInstance_3511_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v_whnf_3512_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v_defEqTrans_3513_);
lean_ctor_set(v_reuseFailAlloc_3529_, 5, v_defEqPerm_3514_);
lean_ctor_set(v_reuseFailAlloc_3529_, 6, v_isUnitLike_3515_);
v___x_3521_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3521_);
v___x_3523_ = v___x_3507_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_mctx_3502_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_zetaDeltaFVarIds_3503_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_postponed_3504_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_diag_3505_);
v___x_3523_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_st_ref_put(v_a_3276_, v___x_3523_);
if (v_isShared_3499_ == 0)
{
v___x_3526_ = v___x_3498_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3495_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3489_);
return v___x_3494_;
}
}
else
{
lean_dec(v_a_3489_);
return v___x_3494_;
}
}
v___jp_3534_:
{
lean_object* v_toCold_3535_; lean_object* v_cancelTk_x3f_3536_; 
v_toCold_3535_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3536_ = lean_ctor_get(v_toCold_3535_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3536_) == 1)
{
lean_object* v_val_3537_; uint8_t v___x_3538_; 
v_val_3537_ = lean_ctor_get(v_cancelTk_x3f_3536_, 0);
v___x_3538_ = l_IO_CancelToken_isSet(v_val_3537_);
if (v___x_3538_ == 0)
{
goto v___jp_3493_;
}
else
{
lean_object* v___x_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_a_3489_);
lean_dec_ref(v___x_3470_);
lean_dec_ref(v___x_3465_);
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
goto v___jp_3493_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v___x_3470_);
lean_dec_ref(v___x_3465_);
v_a_3595_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3488_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3488_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3274_, 2);
goto v___jp_3471_;
}
}
v___jp_3471_:
{
lean_object* v_toCold_3472_; lean_object* v_cancelTk_x3f_3473_; 
v_toCold_3472_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3473_ = lean_ctor_get(v_toCold_3472_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3473_) == 1)
{
lean_object* v_val_3474_; uint8_t v___x_3475_; 
v_val_3474_ = lean_ctor_get(v_cancelTk_x3f_3473_, 0);
v___x_3475_ = l_IO_CancelToken_isSet(v_val_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3465_, v___x_3470_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec_ref(v___x_3470_);
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v___x_3470_);
lean_dec_ref(v___x_3465_);
v___x_3477_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v___x_3486_; 
v___x_3486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3465_, v___x_3470_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec_ref(v___x_3470_);
return v___x_3486_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3603_; 
v_cacheInferType_3603_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3603_ == 0)
{
goto v___jp_3280_;
}
else
{
uint8_t v___x_3604_; 
v___x_3604_ = l_Lean_Expr_hasMVar(v_e_3274_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; 
lean_inc_ref(v_e_3274_);
v___x_3605_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3711_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3711_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3711_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3665_; lean_object* v_cache_3666_; lean_object* v_inferType_3667_; lean_object* v___x_3668_; 
v___x_3665_ = lean_st_ref_get(v_a_3276_);
v_cache_3666_ = lean_ctor_get(v___x_3665_, 1);
lean_inc_ref(v_cache_3666_);
lean_dec(v___x_3665_);
v_inferType_3667_ = lean_ctor_get(v_cache_3666_, 0);
lean_inc_ref(v_inferType_3667_);
lean_dec_ref(v_cache_3666_);
v___x_3668_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3667_, v_a_3606_);
if (lean_obj_tag(v___x_3668_) == 1)
{
lean_object* v_val_3669_; lean_object* v_fst_3670_; lean_object* v_snd_3671_; lean_object* v_expr_3672_; uint64_t v_configKey_3673_; lean_object* v_expr_3674_; uint64_t v_configKey_3675_; uint8_t v___x_3676_; 
v_val_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_val_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v_fst_3670_ = lean_ctor_get(v_val_3669_, 0);
lean_inc(v_fst_3670_);
v_snd_3671_ = lean_ctor_get(v_val_3669_, 1);
lean_inc(v_snd_3671_);
lean_dec(v_val_3669_);
v_expr_3672_ = lean_ctor_get(v_a_3606_, 0);
v_configKey_3673_ = lean_ctor_get_uint64(v_a_3606_, sizeof(void*)*1);
v_expr_3674_ = lean_ctor_get(v_fst_3670_, 0);
lean_inc_ref(v_expr_3674_);
v_configKey_3675_ = lean_ctor_get_uint64(v_fst_3670_, sizeof(void*)*1);
lean_dec(v_fst_3670_);
v___x_3676_ = lean_uint64_dec_eq(v_configKey_3673_, v_configKey_3675_);
if (v___x_3676_ == 0)
{
lean_dec_ref(v_expr_3674_);
lean_dec(v_snd_3671_);
lean_dec_ref(v_inferType_3667_);
lean_del_object(v___x_3608_);
goto v___jp_3651_;
}
else
{
size_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3677_ = ((size_t)64ULL);
v___x_3678_ = lean_expr_equal_budgeted(v_expr_3672_, v_expr_3674_, v___x_3677_);
lean_dec_ref(v_expr_3674_);
switch(v___x_3678_)
{
case 0:
{
lean_dec(v_snd_3671_);
lean_dec_ref(v_inferType_3667_);
lean_del_object(v___x_3608_);
goto v___jp_3651_;
}
case 1:
{
lean_object* v___x_3680_; 
lean_dec_ref(v_inferType_3667_);
lean_dec(v_a_3606_);
lean_dec_ref_known(v_e_3274_, 3);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_snd_3671_);
v___x_3680_ = v___x_3608_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_snd_3671_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
default: 
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_cache_3684_; lean_object* v_mctx_3685_; lean_object* v_zetaDeltaFVarIds_3686_; lean_object* v_postponed_3687_; lean_object* v_diag_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_snd_3671_);
lean_del_object(v___x_3608_);
v___x_3682_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3667_, v_a_3606_);
v___x_3683_ = lean_st_ref_take(v_a_3276_);
v_cache_3684_ = lean_ctor_get(v___x_3683_, 1);
v_mctx_3685_ = lean_ctor_get(v___x_3683_, 0);
v_zetaDeltaFVarIds_3686_ = lean_ctor_get(v___x_3683_, 2);
v_postponed_3687_ = lean_ctor_get(v___x_3683_, 3);
v_diag_3688_ = lean_ctor_get(v___x_3683_, 4);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3690_ = v___x_3683_;
v_isShared_3691_ = v_isSharedCheck_3710_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_diag_3688_);
lean_inc(v_postponed_3687_);
lean_inc(v_zetaDeltaFVarIds_3686_);
lean_inc(v_cache_3684_);
lean_inc(v_mctx_3685_);
lean_dec(v___x_3683_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3710_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_funInfo_3692_; lean_object* v_synthInstance_3693_; lean_object* v_whnf_3694_; lean_object* v_defEqTrans_3695_; lean_object* v_defEqPerm_3696_; lean_object* v_isUnitLike_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3708_; 
v_funInfo_3692_ = lean_ctor_get(v_cache_3684_, 1);
v_synthInstance_3693_ = lean_ctor_get(v_cache_3684_, 2);
v_whnf_3694_ = lean_ctor_get(v_cache_3684_, 3);
v_defEqTrans_3695_ = lean_ctor_get(v_cache_3684_, 4);
v_defEqPerm_3696_ = lean_ctor_get(v_cache_3684_, 5);
v_isUnitLike_3697_ = lean_ctor_get(v_cache_3684_, 6);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_cache_3684_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_cache_3684_, 0);
lean_dec(v_unused_3709_);
v___x_3699_ = v_cache_3684_;
v_isShared_3700_ = v_isSharedCheck_3708_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_isUnitLike_3697_);
lean_inc(v_defEqPerm_3696_);
lean_inc(v_defEqTrans_3695_);
lean_inc(v_whnf_3694_);
lean_inc(v_synthInstance_3693_);
lean_inc(v_funInfo_3692_);
lean_dec(v_cache_3684_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3708_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3682_);
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_funInfo_3692_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_synthInstance_3693_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_whnf_3694_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_defEqTrans_3695_);
lean_ctor_set(v_reuseFailAlloc_3707_, 5, v_defEqPerm_3696_);
lean_ctor_set(v_reuseFailAlloc_3707_, 6, v_isUnitLike_3697_);
v___x_3702_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 1, v___x_3702_);
v___x_3704_ = v___x_3690_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_mctx_3685_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_zetaDeltaFVarIds_3686_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v_postponed_3687_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v_diag_3688_);
v___x_3704_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_st_ref_put(v_a_3276_, v___x_3704_);
goto v___jp_3651_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3668_);
lean_dec_ref(v_inferType_3667_);
lean_del_object(v___x_3608_);
goto v___jp_3651_;
}
v___jp_3610_:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; uint8_t v___x_3613_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v___x_3613_ = l_Lean_Expr_hasMVar(v_a_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3649_; 
lean_inc(v_a_3612_);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v___x_3611_, 0);
lean_dec(v_unused_3650_);
v___x_3615_ = v___x_3611_;
v_isShared_3616_ = v_isSharedCheck_3649_;
goto v_resetjp_3614_;
}
else
{
lean_dec(v___x_3611_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3649_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v_cache_3618_; lean_object* v_mctx_3619_; lean_object* v_zetaDeltaFVarIds_3620_; lean_object* v_postponed_3621_; lean_object* v_diag_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3648_; 
v___x_3617_ = lean_st_ref_take(v_a_3276_);
v_cache_3618_ = lean_ctor_get(v___x_3617_, 1);
v_mctx_3619_ = lean_ctor_get(v___x_3617_, 0);
v_zetaDeltaFVarIds_3620_ = lean_ctor_get(v___x_3617_, 2);
v_postponed_3621_ = lean_ctor_get(v___x_3617_, 3);
v_diag_3622_ = lean_ctor_get(v___x_3617_, 4);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3624_ = v___x_3617_;
v_isShared_3625_ = v_isSharedCheck_3648_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_diag_3622_);
lean_inc(v_postponed_3621_);
lean_inc(v_zetaDeltaFVarIds_3620_);
lean_inc(v_cache_3618_);
lean_inc(v_mctx_3619_);
lean_dec(v___x_3617_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3648_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v_inferType_3626_; lean_object* v_funInfo_3627_; lean_object* v_synthInstance_3628_; lean_object* v_whnf_3629_; lean_object* v_defEqTrans_3630_; lean_object* v_defEqPerm_3631_; lean_object* v_isUnitLike_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3647_; 
v_inferType_3626_ = lean_ctor_get(v_cache_3618_, 0);
v_funInfo_3627_ = lean_ctor_get(v_cache_3618_, 1);
v_synthInstance_3628_ = lean_ctor_get(v_cache_3618_, 2);
v_whnf_3629_ = lean_ctor_get(v_cache_3618_, 3);
v_defEqTrans_3630_ = lean_ctor_get(v_cache_3618_, 4);
v_defEqPerm_3631_ = lean_ctor_get(v_cache_3618_, 5);
v_isUnitLike_3632_ = lean_ctor_get(v_cache_3618_, 6);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_cache_3618_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3634_ = v_cache_3618_;
v_isShared_3635_ = v_isSharedCheck_3647_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_isUnitLike_3632_);
lean_inc(v_defEqPerm_3631_);
lean_inc(v_defEqTrans_3630_);
lean_inc(v_whnf_3629_);
lean_inc(v_synthInstance_3628_);
lean_inc(v_funInfo_3627_);
lean_inc(v_inferType_3626_);
lean_dec(v_cache_3618_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3647_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_inc(v_a_3612_);
v___x_3636_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3626_, v_a_3606_, v_a_3612_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_funInfo_3627_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v_synthInstance_3628_);
lean_ctor_set(v_reuseFailAlloc_3646_, 3, v_whnf_3629_);
lean_ctor_set(v_reuseFailAlloc_3646_, 4, v_defEqTrans_3630_);
lean_ctor_set(v_reuseFailAlloc_3646_, 5, v_defEqPerm_3631_);
lean_ctor_set(v_reuseFailAlloc_3646_, 6, v_isUnitLike_3632_);
v___x_3638_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v___x_3638_);
v___x_3640_ = v___x_3624_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_mctx_3619_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_zetaDeltaFVarIds_3620_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_postponed_3621_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_diag_3622_);
v___x_3640_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3641_ = lean_st_ref_put(v_a_3276_, v___x_3640_);
if (v_isShared_3616_ == 0)
{
v___x_3643_ = v___x_3615_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3612_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3606_);
return v___x_3611_;
}
}
else
{
lean_dec(v_a_3606_);
return v___x_3611_;
}
}
v___jp_3651_:
{
lean_object* v_toCold_3652_; lean_object* v_cancelTk_x3f_3653_; 
v_toCold_3652_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3653_ = lean_ctor_get(v_toCold_3652_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3653_) == 1)
{
lean_object* v_val_3654_; uint8_t v___x_3655_; 
v_val_3654_ = lean_ctor_get(v_cancelTk_x3f_3653_, 0);
v___x_3655_ = l_IO_CancelToken_isSet(v_val_3654_);
if (v___x_3655_ == 0)
{
goto v___jp_3610_;
}
else
{
lean_object* v___x_3656_; lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v_a_3606_);
lean_dec_ref_known(v_e_3274_, 3);
v___x_3656_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
goto v___jp_3610_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref_known(v_e_3274_, 3);
v_a_3712_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3605_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3605_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
goto v___jp_3280_;
}
}
}
case 9:
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_a_3720_ = lean_ctor_get(v_e_3274_, 0);
lean_inc_ref(v_a_3720_);
lean_dec_ref_known(v_e_3274_, 1);
v___x_3721_ = l_Lean_Literal_type(v_a_3720_);
lean_dec_ref(v_a_3720_);
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
case 10:
{
lean_object* v_expr_3723_; 
v_expr_3723_ = lean_ctor_get(v_e_3274_, 1);
lean_inc_ref(v_expr_3723_);
lean_dec_ref_known(v_e_3274_, 2);
v_e_3274_ = v_expr_3723_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3725_; lean_object* v_idx_3726_; lean_object* v_struct_3727_; uint8_t v_cacheInferType_3744_; 
v_typeName_3725_ = lean_ctor_get(v_e_3274_, 0);
lean_inc(v_typeName_3725_);
v_idx_3726_ = lean_ctor_get(v_e_3274_, 1);
lean_inc(v_idx_3726_);
v_struct_3727_ = lean_ctor_get(v_e_3274_, 2);
lean_inc_ref(v_struct_3727_);
v_cacheInferType_3744_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3744_ == 0)
{
lean_dec_ref_known(v_e_3274_, 3);
goto v___jp_3728_;
}
else
{
uint8_t v___x_3745_; 
v___x_3745_ = l_Lean_Expr_hasMVar(v_e_3274_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3852_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3852_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3852_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3806_; lean_object* v_cache_3807_; lean_object* v_inferType_3808_; lean_object* v___x_3809_; 
v___x_3806_ = lean_st_ref_get(v_a_3276_);
v_cache_3807_ = lean_ctor_get(v___x_3806_, 1);
lean_inc_ref(v_cache_3807_);
lean_dec(v___x_3806_);
v_inferType_3808_ = lean_ctor_get(v_cache_3807_, 0);
lean_inc_ref(v_inferType_3808_);
lean_dec_ref(v_cache_3807_);
v___x_3809_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3808_, v_a_3747_);
if (lean_obj_tag(v___x_3809_) == 1)
{
lean_object* v_val_3810_; lean_object* v_fst_3811_; lean_object* v_snd_3812_; lean_object* v_expr_3813_; uint64_t v_configKey_3814_; lean_object* v_expr_3815_; uint64_t v_configKey_3816_; uint8_t v___x_3817_; 
v_val_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_val_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v_fst_3811_ = lean_ctor_get(v_val_3810_, 0);
lean_inc(v_fst_3811_);
v_snd_3812_ = lean_ctor_get(v_val_3810_, 1);
lean_inc(v_snd_3812_);
lean_dec(v_val_3810_);
v_expr_3813_ = lean_ctor_get(v_a_3747_, 0);
v_configKey_3814_ = lean_ctor_get_uint64(v_a_3747_, sizeof(void*)*1);
v_expr_3815_ = lean_ctor_get(v_fst_3811_, 0);
lean_inc_ref(v_expr_3815_);
v_configKey_3816_ = lean_ctor_get_uint64(v_fst_3811_, sizeof(void*)*1);
lean_dec(v_fst_3811_);
v___x_3817_ = lean_uint64_dec_eq(v_configKey_3814_, v_configKey_3816_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v_expr_3815_);
lean_dec(v_snd_3812_);
lean_dec_ref(v_inferType_3808_);
lean_del_object(v___x_3749_);
goto v___jp_3792_;
}
else
{
size_t v___x_3818_; uint8_t v___x_3819_; 
v___x_3818_ = ((size_t)64ULL);
v___x_3819_ = lean_expr_equal_budgeted(v_expr_3813_, v_expr_3815_, v___x_3818_);
lean_dec_ref(v_expr_3815_);
switch(v___x_3819_)
{
case 0:
{
lean_dec(v_snd_3812_);
lean_dec_ref(v_inferType_3808_);
lean_del_object(v___x_3749_);
goto v___jp_3792_;
}
case 1:
{
lean_object* v___x_3821_; 
lean_dec_ref(v_inferType_3808_);
lean_dec(v_a_3747_);
lean_dec_ref(v_struct_3727_);
lean_dec(v_idx_3726_);
lean_dec(v_typeName_3725_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v_snd_3812_);
v___x_3821_ = v___x_3749_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_snd_3812_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
default: 
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v_cache_3825_; lean_object* v_mctx_3826_; lean_object* v_zetaDeltaFVarIds_3827_; lean_object* v_postponed_3828_; lean_object* v_diag_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_snd_3812_);
lean_del_object(v___x_3749_);
v___x_3823_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3808_, v_a_3747_);
v___x_3824_ = lean_st_ref_take(v_a_3276_);
v_cache_3825_ = lean_ctor_get(v___x_3824_, 1);
v_mctx_3826_ = lean_ctor_get(v___x_3824_, 0);
v_zetaDeltaFVarIds_3827_ = lean_ctor_get(v___x_3824_, 2);
v_postponed_3828_ = lean_ctor_get(v___x_3824_, 3);
v_diag_3829_ = lean_ctor_get(v___x_3824_, 4);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3831_ = v___x_3824_;
v_isShared_3832_ = v_isSharedCheck_3851_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_diag_3829_);
lean_inc(v_postponed_3828_);
lean_inc(v_zetaDeltaFVarIds_3827_);
lean_inc(v_cache_3825_);
lean_inc(v_mctx_3826_);
lean_dec(v___x_3824_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3851_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_funInfo_3833_; lean_object* v_synthInstance_3834_; lean_object* v_whnf_3835_; lean_object* v_defEqTrans_3836_; lean_object* v_defEqPerm_3837_; lean_object* v_isUnitLike_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3849_; 
v_funInfo_3833_ = lean_ctor_get(v_cache_3825_, 1);
v_synthInstance_3834_ = lean_ctor_get(v_cache_3825_, 2);
v_whnf_3835_ = lean_ctor_get(v_cache_3825_, 3);
v_defEqTrans_3836_ = lean_ctor_get(v_cache_3825_, 4);
v_defEqPerm_3837_ = lean_ctor_get(v_cache_3825_, 5);
v_isUnitLike_3838_ = lean_ctor_get(v_cache_3825_, 6);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_cache_3825_);
if (v_isSharedCheck_3849_ == 0)
{
lean_object* v_unused_3850_; 
v_unused_3850_ = lean_ctor_get(v_cache_3825_, 0);
lean_dec(v_unused_3850_);
v___x_3840_ = v_cache_3825_;
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_isUnitLike_3838_);
lean_inc(v_defEqPerm_3837_);
lean_inc(v_defEqTrans_3836_);
lean_inc(v_whnf_3835_);
lean_inc(v_synthInstance_3834_);
lean_inc(v_funInfo_3833_);
lean_dec(v_cache_3825_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3823_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_funInfo_3833_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_synthInstance_3834_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_whnf_3835_);
lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_defEqTrans_3836_);
lean_ctor_set(v_reuseFailAlloc_3848_, 5, v_defEqPerm_3837_);
lean_ctor_set(v_reuseFailAlloc_3848_, 6, v_isUnitLike_3838_);
v___x_3843_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3845_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 1, v___x_3843_);
v___x_3845_ = v___x_3831_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_mctx_3826_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_zetaDeltaFVarIds_3827_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v_postponed_3828_);
lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_diag_3829_);
v___x_3845_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_st_ref_put(v_a_3276_, v___x_3845_);
goto v___jp_3792_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3809_);
lean_dec_ref(v_inferType_3808_);
lean_del_object(v___x_3749_);
goto v___jp_3792_;
}
v___jp_3751_:
{
lean_object* v___x_3752_; 
v___x_3752_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3725_, v_idx_3726_, v_struct_3727_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; uint8_t v___x_3754_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v___x_3754_ = l_Lean_Expr_hasMVar(v_a_3753_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3790_; 
lean_inc(v_a_3753_);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v___x_3752_, 0);
lean_dec(v_unused_3791_);
v___x_3756_ = v___x_3752_;
v_isShared_3757_ = v_isSharedCheck_3790_;
goto v_resetjp_3755_;
}
else
{
lean_dec(v___x_3752_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3790_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v_cache_3759_; lean_object* v_mctx_3760_; lean_object* v_zetaDeltaFVarIds_3761_; lean_object* v_postponed_3762_; lean_object* v_diag_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3789_; 
v___x_3758_ = lean_st_ref_take(v_a_3276_);
v_cache_3759_ = lean_ctor_get(v___x_3758_, 1);
v_mctx_3760_ = lean_ctor_get(v___x_3758_, 0);
v_zetaDeltaFVarIds_3761_ = lean_ctor_get(v___x_3758_, 2);
v_postponed_3762_ = lean_ctor_get(v___x_3758_, 3);
v_diag_3763_ = lean_ctor_get(v___x_3758_, 4);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3765_ = v___x_3758_;
v_isShared_3766_ = v_isSharedCheck_3789_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_diag_3763_);
lean_inc(v_postponed_3762_);
lean_inc(v_zetaDeltaFVarIds_3761_);
lean_inc(v_cache_3759_);
lean_inc(v_mctx_3760_);
lean_dec(v___x_3758_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3789_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v_inferType_3767_; lean_object* v_funInfo_3768_; lean_object* v_synthInstance_3769_; lean_object* v_whnf_3770_; lean_object* v_defEqTrans_3771_; lean_object* v_defEqPerm_3772_; lean_object* v_isUnitLike_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3788_; 
v_inferType_3767_ = lean_ctor_get(v_cache_3759_, 0);
v_funInfo_3768_ = lean_ctor_get(v_cache_3759_, 1);
v_synthInstance_3769_ = lean_ctor_get(v_cache_3759_, 2);
v_whnf_3770_ = lean_ctor_get(v_cache_3759_, 3);
v_defEqTrans_3771_ = lean_ctor_get(v_cache_3759_, 4);
v_defEqPerm_3772_ = lean_ctor_get(v_cache_3759_, 5);
v_isUnitLike_3773_ = lean_ctor_get(v_cache_3759_, 6);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_cache_3759_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3775_ = v_cache_3759_;
v_isShared_3776_ = v_isSharedCheck_3788_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_isUnitLike_3773_);
lean_inc(v_defEqPerm_3772_);
lean_inc(v_defEqTrans_3771_);
lean_inc(v_whnf_3770_);
lean_inc(v_synthInstance_3769_);
lean_inc(v_funInfo_3768_);
lean_inc(v_inferType_3767_);
lean_dec(v_cache_3759_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3788_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_inc(v_a_3753_);
v___x_3777_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3767_, v_a_3747_, v_a_3753_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v___x_3777_);
v___x_3779_ = v___x_3775_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_funInfo_3768_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_synthInstance_3769_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v_whnf_3770_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v_defEqTrans_3771_);
lean_ctor_set(v_reuseFailAlloc_3787_, 5, v_defEqPerm_3772_);
lean_ctor_set(v_reuseFailAlloc_3787_, 6, v_isUnitLike_3773_);
v___x_3779_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3781_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 1, v___x_3779_);
v___x_3781_ = v___x_3765_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_mctx_3760_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_zetaDeltaFVarIds_3761_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_postponed_3762_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_diag_3763_);
v___x_3781_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_st_ref_put(v_a_3276_, v___x_3781_);
if (v_isShared_3757_ == 0)
{
v___x_3784_ = v___x_3756_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3753_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3747_);
return v___x_3752_;
}
}
else
{
lean_dec(v_a_3747_);
return v___x_3752_;
}
}
v___jp_3792_:
{
lean_object* v_toCold_3793_; lean_object* v_cancelTk_x3f_3794_; 
v_toCold_3793_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3794_ = lean_ctor_get(v_toCold_3793_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3794_) == 1)
{
lean_object* v_val_3795_; uint8_t v___x_3796_; 
v_val_3795_ = lean_ctor_get(v_cancelTk_x3f_3794_, 0);
v___x_3796_ = l_IO_CancelToken_isSet(v_val_3795_);
if (v___x_3796_ == 0)
{
goto v___jp_3751_;
}
else
{
lean_object* v___x_3797_; lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v_a_3747_);
lean_dec_ref(v_struct_3727_);
lean_dec(v_idx_3726_);
lean_dec(v_typeName_3725_);
v___x_3797_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
goto v___jp_3751_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v_struct_3727_);
lean_dec(v_idx_3726_);
lean_dec(v_typeName_3725_);
v_a_3853_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3746_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3746_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3274_, 3);
goto v___jp_3728_;
}
}
v___jp_3728_:
{
lean_object* v_toCold_3729_; lean_object* v_cancelTk_x3f_3730_; 
v_toCold_3729_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3730_ = lean_ctor_get(v_toCold_3729_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3730_) == 1)
{
lean_object* v_val_3731_; uint8_t v___x_3732_; 
v_val_3731_ = lean_ctor_get(v_cancelTk_x3f_3730_, 0);
v___x_3732_ = l_IO_CancelToken_isSet(v_val_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3725_, v_idx_3726_, v_struct_3727_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec_ref(v_struct_3727_);
lean_dec(v_idx_3726_);
lean_dec(v_typeName_3725_);
v___x_3734_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3725_, v_idx_3726_, v_struct_3727_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3743_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3861_; 
v_cacheInferType_3861_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3861_ == 0)
{
goto v___jp_3296_;
}
else
{
uint8_t v___x_3862_; 
v___x_3862_ = l_Lean_Expr_hasMVar(v_e_3274_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_inc_ref(v_e_3274_);
v___x_3863_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3274_, v_a_3275_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3969_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3969_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3969_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3923_; lean_object* v_cache_3924_; lean_object* v_inferType_3925_; lean_object* v___x_3926_; 
v___x_3923_ = lean_st_ref_get(v_a_3276_);
v_cache_3924_ = lean_ctor_get(v___x_3923_, 1);
lean_inc_ref(v_cache_3924_);
lean_dec(v___x_3923_);
v_inferType_3925_ = lean_ctor_get(v_cache_3924_, 0);
lean_inc_ref(v_inferType_3925_);
lean_dec_ref(v_cache_3924_);
v___x_3926_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3925_, v_a_3864_);
if (lean_obj_tag(v___x_3926_) == 1)
{
lean_object* v_val_3927_; lean_object* v_fst_3928_; lean_object* v_snd_3929_; lean_object* v_expr_3930_; uint64_t v_configKey_3931_; lean_object* v_expr_3932_; uint64_t v_configKey_3933_; uint8_t v___x_3934_; 
v_val_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_val_3927_);
lean_dec_ref_known(v___x_3926_, 1);
v_fst_3928_ = lean_ctor_get(v_val_3927_, 0);
lean_inc(v_fst_3928_);
v_snd_3929_ = lean_ctor_get(v_val_3927_, 1);
lean_inc(v_snd_3929_);
lean_dec(v_val_3927_);
v_expr_3930_ = lean_ctor_get(v_a_3864_, 0);
v_configKey_3931_ = lean_ctor_get_uint64(v_a_3864_, sizeof(void*)*1);
v_expr_3932_ = lean_ctor_get(v_fst_3928_, 0);
lean_inc_ref(v_expr_3932_);
v_configKey_3933_ = lean_ctor_get_uint64(v_fst_3928_, sizeof(void*)*1);
lean_dec(v_fst_3928_);
v___x_3934_ = lean_uint64_dec_eq(v_configKey_3931_, v_configKey_3933_);
if (v___x_3934_ == 0)
{
lean_dec_ref(v_expr_3932_);
lean_dec(v_snd_3929_);
lean_dec_ref(v_inferType_3925_);
lean_del_object(v___x_3866_);
goto v___jp_3909_;
}
else
{
size_t v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = ((size_t)64ULL);
v___x_3936_ = lean_expr_equal_budgeted(v_expr_3930_, v_expr_3932_, v___x_3935_);
lean_dec_ref(v_expr_3932_);
switch(v___x_3936_)
{
case 0:
{
lean_dec(v_snd_3929_);
lean_dec_ref(v_inferType_3925_);
lean_del_object(v___x_3866_);
goto v___jp_3909_;
}
case 1:
{
lean_object* v___x_3938_; 
lean_dec_ref(v_inferType_3925_);
lean_dec(v_a_3864_);
lean_dec_ref(v_e_3274_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v_snd_3929_);
v___x_3938_ = v___x_3866_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_snd_3929_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
default: 
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v_cache_3942_; lean_object* v_mctx_3943_; lean_object* v_zetaDeltaFVarIds_3944_; lean_object* v_postponed_3945_; lean_object* v_diag_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3968_; 
lean_dec(v_snd_3929_);
lean_del_object(v___x_3866_);
v___x_3940_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3925_, v_a_3864_);
v___x_3941_ = lean_st_ref_take(v_a_3276_);
v_cache_3942_ = lean_ctor_get(v___x_3941_, 1);
v_mctx_3943_ = lean_ctor_get(v___x_3941_, 0);
v_zetaDeltaFVarIds_3944_ = lean_ctor_get(v___x_3941_, 2);
v_postponed_3945_ = lean_ctor_get(v___x_3941_, 3);
v_diag_3946_ = lean_ctor_get(v___x_3941_, 4);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3948_ = v___x_3941_;
v_isShared_3949_ = v_isSharedCheck_3968_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_diag_3946_);
lean_inc(v_postponed_3945_);
lean_inc(v_zetaDeltaFVarIds_3944_);
lean_inc(v_cache_3942_);
lean_inc(v_mctx_3943_);
lean_dec(v___x_3941_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3968_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_funInfo_3950_; lean_object* v_synthInstance_3951_; lean_object* v_whnf_3952_; lean_object* v_defEqTrans_3953_; lean_object* v_defEqPerm_3954_; lean_object* v_isUnitLike_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3966_; 
v_funInfo_3950_ = lean_ctor_get(v_cache_3942_, 1);
v_synthInstance_3951_ = lean_ctor_get(v_cache_3942_, 2);
v_whnf_3952_ = lean_ctor_get(v_cache_3942_, 3);
v_defEqTrans_3953_ = lean_ctor_get(v_cache_3942_, 4);
v_defEqPerm_3954_ = lean_ctor_get(v_cache_3942_, 5);
v_isUnitLike_3955_ = lean_ctor_get(v_cache_3942_, 6);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_cache_3942_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v_cache_3942_, 0);
lean_dec(v_unused_3967_);
v___x_3957_ = v_cache_3942_;
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_isUnitLike_3955_);
lean_inc(v_defEqPerm_3954_);
lean_inc(v_defEqTrans_3953_);
lean_inc(v_whnf_3952_);
lean_inc(v_synthInstance_3951_);
lean_inc(v_funInfo_3950_);
lean_dec(v_cache_3942_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3966_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3940_);
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_funInfo_3950_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_synthInstance_3951_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_whnf_3952_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_defEqTrans_3953_);
lean_ctor_set(v_reuseFailAlloc_3965_, 5, v_defEqPerm_3954_);
lean_ctor_set(v_reuseFailAlloc_3965_, 6, v_isUnitLike_3955_);
v___x_3960_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3962_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3960_);
v___x_3962_ = v___x_3948_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_mctx_3943_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_zetaDeltaFVarIds_3944_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_postponed_3945_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_diag_3946_);
v___x_3962_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_st_ref_put(v_a_3276_, v___x_3962_);
goto v___jp_3909_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3926_);
lean_dec_ref(v_inferType_3925_);
lean_del_object(v___x_3866_);
goto v___jp_3909_;
}
v___jp_3868_:
{
lean_object* v___x_3869_; 
v___x_3869_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; uint8_t v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
v___x_3871_ = l_Lean_Expr_hasMVar(v_a_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3907_; 
lean_inc(v_a_3870_);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v___x_3869_, 0);
lean_dec(v_unused_3908_);
v___x_3873_ = v___x_3869_;
v_isShared_3874_ = v_isSharedCheck_3907_;
goto v_resetjp_3872_;
}
else
{
lean_dec(v___x_3869_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3907_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v_cache_3876_; lean_object* v_mctx_3877_; lean_object* v_zetaDeltaFVarIds_3878_; lean_object* v_postponed_3879_; lean_object* v_diag_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3906_; 
v___x_3875_ = lean_st_ref_take(v_a_3276_);
v_cache_3876_ = lean_ctor_get(v___x_3875_, 1);
v_mctx_3877_ = lean_ctor_get(v___x_3875_, 0);
v_zetaDeltaFVarIds_3878_ = lean_ctor_get(v___x_3875_, 2);
v_postponed_3879_ = lean_ctor_get(v___x_3875_, 3);
v_diag_3880_ = lean_ctor_get(v___x_3875_, 4);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3882_ = v___x_3875_;
v_isShared_3883_ = v_isSharedCheck_3906_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_diag_3880_);
lean_inc(v_postponed_3879_);
lean_inc(v_zetaDeltaFVarIds_3878_);
lean_inc(v_cache_3876_);
lean_inc(v_mctx_3877_);
lean_dec(v___x_3875_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3906_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v_inferType_3884_; lean_object* v_funInfo_3885_; lean_object* v_synthInstance_3886_; lean_object* v_whnf_3887_; lean_object* v_defEqTrans_3888_; lean_object* v_defEqPerm_3889_; lean_object* v_isUnitLike_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3905_; 
v_inferType_3884_ = lean_ctor_get(v_cache_3876_, 0);
v_funInfo_3885_ = lean_ctor_get(v_cache_3876_, 1);
v_synthInstance_3886_ = lean_ctor_get(v_cache_3876_, 2);
v_whnf_3887_ = lean_ctor_get(v_cache_3876_, 3);
v_defEqTrans_3888_ = lean_ctor_get(v_cache_3876_, 4);
v_defEqPerm_3889_ = lean_ctor_get(v_cache_3876_, 5);
v_isUnitLike_3890_ = lean_ctor_get(v_cache_3876_, 6);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_cache_3876_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3892_ = v_cache_3876_;
v_isShared_3893_ = v_isSharedCheck_3905_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_isUnitLike_3890_);
lean_inc(v_defEqPerm_3889_);
lean_inc(v_defEqTrans_3888_);
lean_inc(v_whnf_3887_);
lean_inc(v_synthInstance_3886_);
lean_inc(v_funInfo_3885_);
lean_inc(v_inferType_3884_);
lean_dec(v_cache_3876_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3905_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
lean_inc(v_a_3870_);
v___x_3894_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3884_, v_a_3864_, v_a_3870_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3894_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_funInfo_3885_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v_synthInstance_3886_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_whnf_3887_);
lean_ctor_set(v_reuseFailAlloc_3904_, 4, v_defEqTrans_3888_);
lean_ctor_set(v_reuseFailAlloc_3904_, 5, v_defEqPerm_3889_);
lean_ctor_set(v_reuseFailAlloc_3904_, 6, v_isUnitLike_3890_);
v___x_3896_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3898_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3896_);
v___x_3898_ = v___x_3882_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_mctx_3877_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3903_, 2, v_zetaDeltaFVarIds_3878_);
lean_ctor_set(v_reuseFailAlloc_3903_, 3, v_postponed_3879_);
lean_ctor_set(v_reuseFailAlloc_3903_, 4, v_diag_3880_);
v___x_3898_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3899_ = lean_st_ref_put(v_a_3276_, v___x_3898_);
if (v_isShared_3874_ == 0)
{
v___x_3901_ = v___x_3873_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3870_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3864_);
return v___x_3869_;
}
}
else
{
lean_dec(v_a_3864_);
return v___x_3869_;
}
}
v___jp_3909_:
{
lean_object* v_toCold_3910_; lean_object* v_cancelTk_x3f_3911_; 
v_toCold_3910_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3911_ = lean_ctor_get(v_toCold_3910_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3911_) == 1)
{
lean_object* v_val_3912_; uint8_t v___x_3913_; 
v_val_3912_ = lean_ctor_get(v_cancelTk_x3f_3911_, 0);
v___x_3913_ = l_IO_CancelToken_isSet(v_val_3912_);
if (v___x_3913_ == 0)
{
goto v___jp_3868_;
}
else
{
lean_object* v___x_3914_; lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_a_3864_);
lean_dec_ref(v_e_3274_);
v___x_3914_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3914_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3914_);
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
else
{
goto v___jp_3868_;
}
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v_e_3274_);
v_a_3970_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3863_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3863_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
else
{
goto v___jp_3296_;
}
}
}
}
v___jp_3280_:
{
lean_object* v_toCold_3281_; lean_object* v_cancelTk_x3f_3282_; 
v_toCold_3281_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3282_ = lean_ctor_get(v_toCold_3281_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3282_) == 1)
{
lean_object* v_val_3283_; uint8_t v___x_3284_; 
v_val_3283_ = lean_ctor_get(v_cancelTk_x3f_3282_, 0);
v___x_3284_ = l_IO_CancelToken_isSet(v_val_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3285_;
}
else
{
lean_object* v___x_3286_; lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v_e_3274_);
v___x_3286_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3295_;
}
}
v___jp_3296_:
{
lean_object* v_toCold_3297_; lean_object* v_cancelTk_x3f_3298_; 
v_toCold_3297_ = lean_ctor_get(v_a_3277_, 0);
v_cancelTk_x3f_3298_ = lean_ctor_get(v_toCold_3297_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3298_) == 1)
{
lean_object* v_val_3299_; uint8_t v___x_3300_; 
v_val_3299_ = lean_ctor_get(v_cancelTk_x3f_3298_, 0);
v___x_3300_ = l_IO_CancelToken_isSet(v_val_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_e_3274_);
v___x_3302_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
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
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3985_, lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3986_, v_x_3987_, v_x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3991_, v_x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3994_, v_x_3995_, v_x_3996_);
lean_dec_ref(v_x_3996_);
lean_dec_ref(v_x_3995_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(lean_object* v_00_u03b2_3998_, lean_object* v_x_3999_, lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3999_, v_x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___boxed(lean_object* v_00_u03b2_4002_, lean_object* v_x_4003_, lean_object* v_x_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(v_00_u03b2_4002_, v_x_4003_, v_x_4004_);
lean_dec_ref(v_x_4004_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_4006_, lean_object* v_x_4007_, size_t v_x_4008_, size_t v_x_4009_, lean_object* v_x_4010_, lean_object* v_x_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_4007_, v_x_4008_, v_x_4009_, v_x_4010_, v_x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_){
_start:
{
size_t v_x_5606__boxed_4019_; size_t v_x_5607__boxed_4020_; lean_object* v_res_4021_; 
v_x_5606__boxed_4019_ = lean_unbox_usize(v_x_4015_);
lean_dec(v_x_4015_);
v_x_5607__boxed_4020_ = lean_unbox_usize(v_x_4016_);
lean_dec(v_x_4016_);
v_res_4021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_4013_, v_x_4014_, v_x_5606__boxed_4019_, v_x_5607__boxed_4020_, v_x_4017_, v_x_4018_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_4022_, lean_object* v_x_4023_, size_t v_x_4024_, lean_object* v_x_4025_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_4023_, v_x_4024_, v_x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4027_, lean_object* v_x_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
size_t v_x_5623__boxed_4031_; lean_object* v_res_4032_; 
v_x_5623__boxed_4031_ = lean_unbox_usize(v_x_4029_);
lean_dec(v_x_4029_);
v_res_4032_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_4027_, v_x_4028_, v_x_5623__boxed_4031_, v_x_4030_);
lean_dec_ref(v_x_4030_);
lean_dec_ref(v_x_4028_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(lean_object* v_00_u03b2_4033_, lean_object* v_x_4034_, size_t v_x_4035_, lean_object* v_x_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_4034_, v_x_4035_, v_x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4038_, lean_object* v_x_4039_, lean_object* v_x_4040_, lean_object* v_x_4041_){
_start:
{
size_t v_x_5634__boxed_4042_; lean_object* v_res_4043_; 
v_x_5634__boxed_4042_ = lean_unbox_usize(v_x_4040_);
lean_dec(v_x_4040_);
v_res_4043_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(v_00_u03b2_4038_, v_x_4039_, v_x_5634__boxed_4042_, v_x_4041_);
lean_dec_ref(v_x_4041_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4044_, lean_object* v_n_4045_, lean_object* v_k_4046_, lean_object* v_v_4047_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_4045_, v_k_4046_, v_v_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_4049_, size_t v_depth_4050_, lean_object* v_keys_4051_, lean_object* v_vals_4052_, lean_object* v_heq_4053_, lean_object* v_i_4054_, lean_object* v_entries_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_4050_, v_keys_4051_, v_vals_4052_, v_i_4054_, v_entries_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_depth_4058_, lean_object* v_keys_4059_, lean_object* v_vals_4060_, lean_object* v_heq_4061_, lean_object* v_i_4062_, lean_object* v_entries_4063_){
_start:
{
size_t v_depth_boxed_4064_; lean_object* v_res_4065_; 
v_depth_boxed_4064_ = lean_unbox_usize(v_depth_4058_);
lean_dec(v_depth_4058_);
v_res_4065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_4057_, v_depth_boxed_4064_, v_keys_4059_, v_vals_4060_, v_heq_4061_, v_i_4062_, v_entries_4063_);
lean_dec_ref(v_vals_4060_);
lean_dec_ref(v_keys_4059_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4066_, lean_object* v_keys_4067_, lean_object* v_vals_4068_, lean_object* v_heq_4069_, lean_object* v_i_4070_, lean_object* v_k_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_4067_, v_vals_4068_, v_i_4070_, v_k_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4073_, lean_object* v_keys_4074_, lean_object* v_vals_4075_, lean_object* v_heq_4076_, lean_object* v_i_4077_, lean_object* v_k_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_4073_, v_keys_4074_, v_vals_4075_, v_heq_4076_, v_i_4077_, v_k_4078_);
lean_dec_ref(v_k_4078_);
lean_dec_ref(v_vals_4075_);
lean_dec_ref(v_keys_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_x_4081_, v_x_4082_, v_x_4083_, v_x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = l_Lean_maxRecDepthErrorMessage;
v___x_4092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_4094_ = l_Lean_MessageData_ofFormat(v___x_4093_);
return v___x_4094_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4095_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_4096_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_4097_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
lean_ctor_set(v___x_4097_, 1, v___x_4095_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_4098_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v_ref_4098_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4103_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_4106_, lean_object* v_ref_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4107_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_4114_, lean_object* v_ref_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_4114_, v_ref_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___x_4174_; uint8_t v_beta_4175_; 
v___x_4174_ = l_Lean_Meta_Context_config(v___y_4123_);
v_beta_4175_ = lean_ctor_get_uint8(v___x_4174_, 13);
if (v_beta_4175_ == 0)
{
lean_dec_ref(v___x_4174_);
goto v___jp_4128_;
}
else
{
uint8_t v_iota_4176_; 
v_iota_4176_ = lean_ctor_get_uint8(v___x_4174_, 12);
if (v_iota_4176_ == 0)
{
lean_dec_ref(v___x_4174_);
goto v___jp_4128_;
}
else
{
uint8_t v_zeta_4177_; 
v_zeta_4177_ = lean_ctor_get_uint8(v___x_4174_, 15);
if (v_zeta_4177_ == 0)
{
lean_dec_ref(v___x_4174_);
goto v___jp_4128_;
}
else
{
uint8_t v_zetaHave_4178_; 
v_zetaHave_4178_ = lean_ctor_get_uint8(v___x_4174_, 18);
if (v_zetaHave_4178_ == 0)
{
lean_dec_ref(v___x_4174_);
goto v___jp_4128_;
}
else
{
uint8_t v_zetaDelta_4179_; 
v_zetaDelta_4179_ = lean_ctor_get_uint8(v___x_4174_, 16);
if (v_zetaDelta_4179_ == 0)
{
lean_dec_ref(v___x_4174_);
goto v___jp_4128_;
}
else
{
uint8_t v_etaStruct_4180_; uint8_t v_proj_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_etaStruct_4180_ = lean_ctor_get_uint8(v___x_4174_, 10);
v_proj_4181_ = lean_ctor_get_uint8(v___x_4174_, 14);
lean_dec_ref(v___x_4174_);
v___x_4182_ = lean_box(v_proj_4181_);
v___x_4183_ = lean_obj_tag_nat(v___x_4182_);
lean_dec(v___x_4182_);
v___x_4184_ = lean_unsigned_to_nat(2u);
v___x_4185_ = lean_nat_dec_eq(v___x_4183_, v___x_4184_);
if (v___x_4185_ == 0)
{
goto v___jp_4128_;
}
else
{
uint8_t v___x_4186_; uint8_t v___x_4187_; 
v___x_4186_ = 0;
v___x_4187_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4180_, v___x_4186_);
if (v___x_4187_ == 0)
{
goto v___jp_4128_;
}
else
{
lean_object* v___x_4188_; 
v___x_4188_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec_ref(v___y_4123_);
return v___x_4188_;
}
}
}
}
}
}
}
v___jp_4128_:
{
lean_object* v___x_4129_; uint8_t v_foApprox_4130_; uint8_t v_ctxApprox_4131_; uint8_t v_quasiPatternApprox_4132_; uint8_t v_constApprox_4133_; uint8_t v_isDefEqStuckEx_4134_; uint8_t v_unificationHints_4135_; uint8_t v_proofIrrelevance_4136_; uint8_t v_assignSyntheticOpaque_4137_; uint8_t v_offsetCnstrs_4138_; uint8_t v_transparency_4139_; uint8_t v_univApprox_4140_; uint8_t v_zetaUnused_4141_; uint8_t v_canUnfoldPredicateConfig_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4173_; 
v___x_4129_ = l_Lean_Meta_Context_config(v___y_4123_);
v_foApprox_4130_ = lean_ctor_get_uint8(v___x_4129_, 0);
v_ctxApprox_4131_ = lean_ctor_get_uint8(v___x_4129_, 1);
v_quasiPatternApprox_4132_ = lean_ctor_get_uint8(v___x_4129_, 2);
v_constApprox_4133_ = lean_ctor_get_uint8(v___x_4129_, 3);
v_isDefEqStuckEx_4134_ = lean_ctor_get_uint8(v___x_4129_, 4);
v_unificationHints_4135_ = lean_ctor_get_uint8(v___x_4129_, 5);
v_proofIrrelevance_4136_ = lean_ctor_get_uint8(v___x_4129_, 6);
v_assignSyntheticOpaque_4137_ = lean_ctor_get_uint8(v___x_4129_, 7);
v_offsetCnstrs_4138_ = lean_ctor_get_uint8(v___x_4129_, 8);
v_transparency_4139_ = lean_ctor_get_uint8(v___x_4129_, 9);
v_univApprox_4140_ = lean_ctor_get_uint8(v___x_4129_, 11);
v_zetaUnused_4141_ = lean_ctor_get_uint8(v___x_4129_, 17);
v_canUnfoldPredicateConfig_4142_ = lean_ctor_get_uint8(v___x_4129_, 19);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4144_ = v___x_4129_;
v_isShared_4145_ = v_isSharedCheck_4173_;
goto v_resetjp_4143_;
}
else
{
lean_dec(v___x_4129_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4173_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
uint8_t v___x_4146_; uint8_t v___x_4147_; uint8_t v___x_4148_; lean_object* v___x_4150_; 
v___x_4146_ = 1;
v___x_4147_ = 0;
v___x_4148_ = 2;
if (v_isShared_4145_ == 0)
{
v___x_4150_ = v___x_4144_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 0, v_foApprox_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 1, v_ctxApprox_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 2, v_quasiPatternApprox_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 3, v_constApprox_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 4, v_isDefEqStuckEx_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 5, v_unificationHints_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 6, v_proofIrrelevance_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 7, v_assignSyntheticOpaque_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 8, v_offsetCnstrs_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 9, v_transparency_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 11, v_univApprox_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 17, v_zetaUnused_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4172_, 19, v_canUnfoldPredicateConfig_4142_);
v___x_4150_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
uint8_t v_trackZetaDelta_4151_; lean_object* v_zetaDeltaSet_4152_; lean_object* v_lctx_4153_; lean_object* v_localInstances_4154_; lean_object* v_defEqCtx_x3f_4155_; lean_object* v_synthPendingDepth_4156_; lean_object* v_customCanUnfoldPredicate_x3f_4157_; uint8_t v_univApprox_4158_; uint8_t v_inTypeClassResolution_4159_; uint8_t v_cacheInferType_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4170_; 
lean_ctor_set_uint8(v___x_4150_, 10, v___x_4147_);
lean_ctor_set_uint8(v___x_4150_, 12, v___x_4146_);
lean_ctor_set_uint8(v___x_4150_, 13, v___x_4146_);
lean_ctor_set_uint8(v___x_4150_, 14, v___x_4148_);
lean_ctor_set_uint8(v___x_4150_, 15, v___x_4146_);
lean_ctor_set_uint8(v___x_4150_, 16, v___x_4146_);
lean_ctor_set_uint8(v___x_4150_, 18, v___x_4146_);
v_trackZetaDelta_4151_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*7);
v_zetaDeltaSet_4152_ = lean_ctor_get(v___y_4123_, 1);
v_lctx_4153_ = lean_ctor_get(v___y_4123_, 2);
v_localInstances_4154_ = lean_ctor_get(v___y_4123_, 3);
v_defEqCtx_x3f_4155_ = lean_ctor_get(v___y_4123_, 4);
v_synthPendingDepth_4156_ = lean_ctor_get(v___y_4123_, 5);
v_customCanUnfoldPredicate_x3f_4157_ = lean_ctor_get(v___y_4123_, 6);
v_univApprox_4158_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4159_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*7 + 2);
v_cacheInferType_4160_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*7 + 3);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___y_4123_);
if (v_isSharedCheck_4170_ == 0)
{
lean_object* v_unused_4171_; 
v_unused_4171_ = lean_ctor_get(v___y_4123_, 0);
lean_dec(v_unused_4171_);
v___x_4162_ = v___y_4123_;
v_isShared_4163_ = v_isSharedCheck_4170_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4157_);
lean_inc(v_synthPendingDepth_4156_);
lean_inc(v_defEqCtx_x3f_4155_);
lean_inc(v_localInstances_4154_);
lean_inc(v_lctx_4153_);
lean_inc(v_zetaDeltaSet_4152_);
lean_dec(v___y_4123_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4170_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
uint64_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4150_);
v___x_4165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4165_, 0, v___x_4150_);
lean_ctor_set_uint64(v___x_4165_, sizeof(void*)*1, v___x_4164_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4165_);
v___x_4167_ = v___x_4162_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v_zetaDeltaSet_4152_);
lean_ctor_set(v_reuseFailAlloc_4169_, 2, v_lctx_4153_);
lean_ctor_set(v_reuseFailAlloc_4169_, 3, v_localInstances_4154_);
lean_ctor_set(v_reuseFailAlloc_4169_, 4, v_defEqCtx_x3f_4155_);
lean_ctor_set(v_reuseFailAlloc_4169_, 5, v_synthPendingDepth_4156_);
lean_ctor_set(v_reuseFailAlloc_4169_, 6, v_customCanUnfoldPredicate_x3f_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4169_, sizeof(void*)*7, v_trackZetaDelta_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4169_, sizeof(void*)*7 + 1, v_univApprox_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4169_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4169_, sizeof(void*)*7 + 3, v_cacheInferType_4160_);
v___x_4167_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4168_; 
v___x_4168_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4122_, v___x_4167_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec_ref(v___x_4167_);
return v___x_4168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v___y_4203_; lean_object* v_toCold_4220_; lean_object* v_currRecDepth_4221_; lean_object* v_ref_4222_; uint16_t v_optionFlags_4223_; uint8_t v_suppressElabErrors_4224_; uint8_t v_checkDeprecated_4225_; uint8_t v_isRecordingDeps_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4266_; 
v_toCold_4220_ = lean_ctor_get(v_a_4199_, 0);
v_currRecDepth_4221_ = lean_ctor_get(v_a_4199_, 1);
v_ref_4222_ = lean_ctor_get(v_a_4199_, 2);
v_optionFlags_4223_ = lean_ctor_get_uint16(v_a_4199_, sizeof(void*)*3);
v_suppressElabErrors_4224_ = lean_ctor_get_uint8(v_a_4199_, sizeof(void*)*3 + 2);
v_checkDeprecated_4225_ = lean_ctor_get_uint8(v_a_4199_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4226_ = lean_ctor_get_uint8(v_a_4199_, sizeof(void*)*3 + 4);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_a_4199_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4228_ = v_a_4199_;
v_isShared_4229_ = v_isSharedCheck_4266_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_ref_4222_);
lean_inc(v_currRecDepth_4221_);
lean_inc(v_toCold_4220_);
lean_dec(v_a_4199_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4266_;
goto v_resetjp_4227_;
}
v___jp_4202_:
{
if (lean_obj_tag(v___y_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v_a_4204_ = lean_ctor_get(v___y_4203_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___y_4203_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___y_4203_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___y_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
v_a_4212_ = lean_ctor_get(v___y_4203_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___y_4203_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___y_4203_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___y_4203_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
v_resetjp_4227_:
{
lean_object* v_maxRecDepth_4230_; lean_object* v___x_4262_; uint8_t v___x_4263_; 
v_maxRecDepth_4230_ = lean_ctor_get(v_toCold_4220_, 3);
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = lean_nat_dec_eq(v_maxRecDepth_4230_, v___x_4262_);
if (v___x_4263_ == 0)
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_nat_dec_eq(v_currRecDepth_4221_, v_maxRecDepth_4230_);
if (v___x_4264_ == 0)
{
goto v___jp_4231_;
}
else
{
lean_object* v___x_4265_; 
lean_del_object(v___x_4228_);
lean_dec(v_currRecDepth_4221_);
lean_dec_ref(v_toCold_4220_);
lean_dec(v_a_4200_);
lean_dec(v_a_4198_);
lean_dec_ref(v_a_4197_);
lean_dec_ref(v_e_4196_);
v___x_4265_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4222_);
return v___x_4265_;
}
}
else
{
goto v___jp_4231_;
}
v___jp_4231_:
{
lean_object* v___x_4232_; uint8_t v_transparency_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4232_ = l_Lean_Meta_Context_config(v_a_4197_);
v_transparency_4233_ = lean_ctor_get_uint8(v___x_4232_, 9);
lean_dec_ref(v___x_4232_);
v___x_4234_ = lean_unsigned_to_nat(1u);
v___x_4235_ = lean_nat_add(v_currRecDepth_4221_, v___x_4234_);
lean_dec(v_currRecDepth_4221_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 1, v___x_4235_);
v___x_4237_ = v___x_4228_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_toCold_4220_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4261_, 2, v_ref_4222_);
lean_ctor_set_uint16(v_reuseFailAlloc_4261_, sizeof(void*)*3, v_optionFlags_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4261_, sizeof(void*)*3 + 2, v_suppressElabErrors_4224_);
lean_ctor_set_uint8(v_reuseFailAlloc_4261_, sizeof(void*)*3 + 3, v_checkDeprecated_4225_);
lean_ctor_set_uint8(v_reuseFailAlloc_4261_, sizeof(void*)*3 + 4, v_isRecordingDeps_4226_);
v___x_4237_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
uint8_t v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = 1;
v___x_4239_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4233_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4196_, v_a_4197_, v_a_4198_, v___x_4237_, v_a_4200_);
lean_dec(v_a_4200_);
lean_dec_ref(v___x_4237_);
lean_dec(v_a_4198_);
v___y_4203_ = v___x_4240_;
goto v___jp_4202_;
}
else
{
lean_object* v_keyedConfig_4241_; uint8_t v_trackZetaDelta_4242_; lean_object* v_zetaDeltaSet_4243_; lean_object* v_lctx_4244_; lean_object* v_localInstances_4245_; lean_object* v_defEqCtx_x3f_4246_; lean_object* v_synthPendingDepth_4247_; lean_object* v_customCanUnfoldPredicate_x3f_4248_; uint8_t v_univApprox_4249_; uint8_t v_inTypeClassResolution_4250_; uint8_t v_cacheInferType_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4260_; 
v_keyedConfig_4241_ = lean_ctor_get(v_a_4197_, 0);
v_trackZetaDelta_4242_ = lean_ctor_get_uint8(v_a_4197_, sizeof(void*)*7);
v_zetaDeltaSet_4243_ = lean_ctor_get(v_a_4197_, 1);
v_lctx_4244_ = lean_ctor_get(v_a_4197_, 2);
v_localInstances_4245_ = lean_ctor_get(v_a_4197_, 3);
v_defEqCtx_x3f_4246_ = lean_ctor_get(v_a_4197_, 4);
v_synthPendingDepth_4247_ = lean_ctor_get(v_a_4197_, 5);
v_customCanUnfoldPredicate_x3f_4248_ = lean_ctor_get(v_a_4197_, 6);
v_univApprox_4249_ = lean_ctor_get_uint8(v_a_4197_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4250_ = lean_ctor_get_uint8(v_a_4197_, sizeof(void*)*7 + 2);
v_cacheInferType_4251_ = lean_ctor_get_uint8(v_a_4197_, sizeof(void*)*7 + 3);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_a_4197_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4253_ = v_a_4197_;
v_isShared_4254_ = v_isSharedCheck_4260_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4248_);
lean_inc(v_synthPendingDepth_4247_);
lean_inc(v_defEqCtx_x3f_4246_);
lean_inc(v_localInstances_4245_);
lean_inc(v_lctx_4244_);
lean_inc(v_zetaDeltaSet_4243_);
lean_inc(v_keyedConfig_4241_);
lean_dec(v_a_4197_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4260_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4255_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4238_, v_keyedConfig_4241_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4255_);
v___x_4257_ = v___x_4253_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_zetaDeltaSet_4243_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_lctx_4244_);
lean_ctor_set(v_reuseFailAlloc_4259_, 3, v_localInstances_4245_);
lean_ctor_set(v_reuseFailAlloc_4259_, 4, v_defEqCtx_x3f_4246_);
lean_ctor_set(v_reuseFailAlloc_4259_, 5, v_synthPendingDepth_4247_);
lean_ctor_set(v_reuseFailAlloc_4259_, 6, v_customCanUnfoldPredicate_x3f_4248_);
lean_ctor_set_uint8(v_reuseFailAlloc_4259_, sizeof(void*)*7, v_trackZetaDelta_4242_);
lean_ctor_set_uint8(v_reuseFailAlloc_4259_, sizeof(void*)*7 + 1, v_univApprox_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4259_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4250_);
lean_ctor_set_uint8(v_reuseFailAlloc_4259_, sizeof(void*)*7 + 3, v_cacheInferType_4251_);
v___x_4257_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4196_, v___x_4257_, v_a_4198_, v___x_4237_, v_a_4200_);
lean_dec(v_a_4200_);
lean_dec_ref(v___x_4237_);
lean_dec(v_a_4198_);
v___y_4203_ = v___x_4258_;
goto v___jp_4202_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = lean_infer_type(v_e_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
return v_res_4273_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_4274_){
_start:
{
switch(lean_obj_tag(v_x_4274_))
{
case 0:
{
uint8_t v___x_4275_; 
v___x_4275_ = 1;
return v___x_4275_;
}
case 2:
{
lean_object* v_a_4276_; lean_object* v_a_4277_; uint8_t v___x_4278_; 
v_a_4276_ = lean_ctor_get(v_x_4274_, 0);
v_a_4277_ = lean_ctor_get(v_x_4274_, 1);
v___x_4278_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4276_);
if (v___x_4278_ == 0)
{
return v___x_4278_;
}
else
{
v_x_4274_ = v_a_4277_;
goto _start;
}
}
case 3:
{
lean_object* v_a_4280_; 
v_a_4280_ = lean_ctor_get(v_x_4274_, 1);
v_x_4274_ = v_a_4280_;
goto _start;
}
default: 
{
uint8_t v___x_4282_; 
v___x_4282_ = 0;
return v___x_4282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_4283_){
_start:
{
uint8_t v_res_4284_; lean_object* v_r_4285_; 
v_res_4284_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_4283_);
lean_dec(v_x_4283_);
v_r_4285_ = lean_box(v_res_4284_);
return v_r_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; lean_object* v_mctx_4290_; lean_object* v___x_4291_; lean_object* v_fst_4292_; lean_object* v_snd_4293_; lean_object* v___x_4294_; lean_object* v_cache_4295_; lean_object* v_zetaDeltaFVarIds_4296_; lean_object* v_postponed_4297_; lean_object* v_diag_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4307_; 
v___x_4289_ = lean_st_ref_get(v___y_4287_);
v_mctx_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc_ref(v_mctx_4290_);
lean_dec(v___x_4289_);
v___x_4291_ = lean_instantiate_level_mvars(v_mctx_4290_, v_l_4286_);
v_fst_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_fst_4292_);
v_snd_4293_ = lean_ctor_get(v___x_4291_, 1);
lean_inc(v_snd_4293_);
lean_dec_ref(v___x_4291_);
v___x_4294_ = lean_st_ref_take(v___y_4287_);
v_cache_4295_ = lean_ctor_get(v___x_4294_, 1);
v_zetaDeltaFVarIds_4296_ = lean_ctor_get(v___x_4294_, 2);
v_postponed_4297_ = lean_ctor_get(v___x_4294_, 3);
v_diag_4298_ = lean_ctor_get(v___x_4294_, 4);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4307_ == 0)
{
lean_object* v_unused_4308_; 
v_unused_4308_ = lean_ctor_get(v___x_4294_, 0);
lean_dec(v_unused_4308_);
v___x_4300_ = v___x_4294_;
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_diag_4298_);
lean_inc(v_postponed_4297_);
lean_inc(v_zetaDeltaFVarIds_4296_);
lean_inc(v_cache_4295_);
lean_dec(v___x_4294_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v_fst_4292_);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_fst_4292_);
lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_cache_4295_);
lean_ctor_set(v_reuseFailAlloc_4306_, 2, v_zetaDeltaFVarIds_4296_);
lean_ctor_set(v_reuseFailAlloc_4306_, 3, v_postponed_4297_);
lean_ctor_set(v_reuseFailAlloc_4306_, 4, v_diag_4298_);
v___x_4303_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_st_ref_put(v___y_4287_, v___x_4303_);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v_snd_4293_);
return v___x_4305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4309_, v___y_4310_);
lean_dec(v___y_4310_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4313_, v___y_4315_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_00_u03c3_4327_, lean_object* v_x_4328_, lean_object* v_x_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v___y_4340_; 
switch(lean_obj_tag(v_x_4328_))
{
case 3:
{
lean_object* v_u_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_u_4361_ = lean_ctor_get(v_x_4328_, 0);
lean_inc(v_u_4361_);
lean_dec_ref_known(v_x_4328_, 1);
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = lean_nat_dec_eq(v_x_4329_, v___x_4362_);
lean_dec(v_x_4329_);
if (v___x_4363_ == 0)
{
lean_dec(v_u_4361_);
lean_dec_ref(v_00_u03c3_4327_);
goto v___jp_4335_;
}
else
{
lean_object* v_paramNames_4364_; lean_object* v_lvls_4365_; uint8_t v___x_4366_; 
v_paramNames_4364_ = lean_ctor_get(v_00_u03c3_4327_, 0);
lean_inc(v_paramNames_4364_);
v_lvls_4365_ = lean_ctor_get(v_00_u03c3_4327_, 1);
lean_inc(v_lvls_4365_);
lean_dec_ref(v_00_u03c3_4327_);
v___x_4366_ = l_List_isEmpty___redArg(v_paramNames_4364_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Lean_Level_instantiateParams(v_u_4361_, v_paramNames_4364_, v_lvls_4365_);
v___y_4340_ = v___x_4367_;
goto v___jp_4339_;
}
else
{
lean_dec(v_lvls_4365_);
lean_dec(v_paramNames_4364_);
v___y_4340_ = v_u_4361_;
goto v___jp_4339_;
}
}
}
case 7:
{
lean_object* v_body_4368_; lean_object* v_zero_4369_; uint8_t v_isZero_4370_; 
v_body_4368_ = lean_ctor_get(v_x_4328_, 2);
lean_inc_ref(v_body_4368_);
lean_dec_ref_known(v_x_4328_, 3);
v_zero_4369_ = lean_unsigned_to_nat(0u);
v_isZero_4370_ = lean_nat_dec_eq(v_x_4329_, v_zero_4369_);
if (v_isZero_4370_ == 1)
{
uint8_t v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
lean_dec_ref(v_body_4368_);
lean_dec(v_x_4329_);
lean_dec_ref(v_00_u03c3_4327_);
v___x_4371_ = 0;
v___x_4372_ = lean_box(v___x_4371_);
v___x_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
return v___x_4373_;
}
else
{
lean_object* v_one_4374_; lean_object* v_n_4375_; 
v_one_4374_ = lean_unsigned_to_nat(1u);
v_n_4375_ = lean_nat_sub(v_x_4329_, v_one_4374_);
lean_dec(v_x_4329_);
v_x_4328_ = v_body_4368_;
v_x_4329_ = v_n_4375_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4377_; 
v_body_4377_ = lean_ctor_get(v_x_4328_, 3);
lean_inc_ref(v_body_4377_);
lean_dec_ref_known(v_x_4328_, 4);
v_x_4328_ = v_body_4377_;
goto _start;
}
case 10:
{
lean_object* v_expr_4379_; 
v_expr_4379_ = lean_ctor_get(v_x_4328_, 1);
lean_inc_ref(v_expr_4379_);
lean_dec_ref_known(v_x_4328_, 2);
v_x_4328_ = v_expr_4379_;
goto _start;
}
default: 
{
lean_dec(v_x_4329_);
lean_dec_ref(v_x_4328_);
lean_dec_ref(v_00_u03c3_4327_);
goto v___jp_4335_;
}
}
v___jp_4335_:
{
uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = 2;
v___x_4337_ = lean_box(v___x_4336_);
v___x_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
return v___x_4338_;
}
v___jp_4339_:
{
lean_object* v___x_4341_; 
v___x_4341_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v___y_4340_, v_a_4331_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4352_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4352_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4352_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
uint8_t v___x_4346_; uint8_t v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4346_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4342_);
lean_dec(v_a_4342_);
v___x_4347_ = l_Lean_Bool_toLBool(v___x_4346_);
v___x_4348_ = lean_box(v___x_4347_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4348_);
v___x_4350_ = v___x_4344_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
v_a_4353_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4341_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4341_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_00_u03c3_4381_, lean_object* v_x_4382_, lean_object* v_x_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_00_u03c3_4381_, v_x_4382_, v_x_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object* v_00_u03c3_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
if (lean_obj_tag(v_a_4391_) == 0)
{
lean_object* v___x_4393_; 
lean_dec_ref(v_00_u03c3_4390_);
v___x_4393_ = l_List_reverse___redArg(v_a_4392_);
return v___x_4393_;
}
else
{
lean_object* v_head_4394_; lean_object* v_tail_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4409_; 
v_head_4394_ = lean_ctor_get(v_a_4391_, 0);
v_tail_4395_ = lean_ctor_get(v_a_4391_, 1);
v_isSharedCheck_4409_ = !lean_is_exclusive(v_a_4391_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4397_ = v_a_4391_;
v_isShared_4398_ = v_isSharedCheck_4409_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_tail_4395_);
lean_inc(v_head_4394_);
lean_dec(v_a_4391_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4409_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___y_4400_; lean_object* v_paramNames_4405_; lean_object* v_lvls_4406_; uint8_t v___x_4407_; 
v_paramNames_4405_ = lean_ctor_get(v_00_u03c3_4390_, 0);
v_lvls_4406_ = lean_ctor_get(v_00_u03c3_4390_, 1);
v___x_4407_ = l_List_isEmpty___redArg(v_paramNames_4405_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_inc(v_lvls_4406_);
lean_inc(v_paramNames_4405_);
v___x_4408_ = l_Lean_Level_instantiateParams(v_head_4394_, v_paramNames_4405_, v_lvls_4406_);
v___y_4400_ = v___x_4408_;
goto v___jp_4399_;
}
else
{
v___y_4400_ = v_head_4394_;
goto v___jp_4399_;
}
v___jp_4399_:
{
lean_object* v___x_4402_; 
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v_a_4392_);
lean_ctor_set(v___x_4397_, 0, v___y_4400_);
v___x_4402_ = v___x_4397_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___y_4400_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_a_4392_);
v___x_4402_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
v_a_4391_ = v_tail_4395_;
v_a_4392_ = v___x_4402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_00_u03c3_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
switch(lean_obj_tag(v_x_4413_))
{
case 4:
{
lean_object* v_declName_4420_; lean_object* v_us_4421_; lean_object* v___y_4423_; lean_object* v_paramNames_4437_; uint8_t v___x_4438_; 
v_declName_4420_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_declName_4420_);
v_us_4421_ = lean_ctor_get(v_x_4413_, 1);
lean_inc(v_us_4421_);
lean_dec_ref_known(v_x_4413_, 2);
v_paramNames_4437_ = lean_ctor_get(v_00_u03c3_4412_, 0);
v___x_4438_ = l_List_isEmpty___redArg(v_paramNames_4437_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_box(0);
v___x_4440_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4412_, v_us_4421_, v___x_4439_);
v___y_4423_ = v___x_4440_;
goto v___jp_4422_;
}
else
{
lean_dec_ref(v_00_u03c3_4412_);
v___y_4423_ = v_us_4421_;
goto v___jp_4422_;
}
v___jp_4422_:
{
lean_object* v___x_4424_; 
v___x_4424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4420_, v___y_4423_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v_fst_4426_; lean_object* v_snd_4427_; lean_object* v___x_4428_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v_fst_4426_ = lean_ctor_get(v_a_4425_, 0);
lean_inc(v_fst_4426_);
v_snd_4427_ = lean_ctor_get(v_a_4425_, 1);
lean_inc(v_snd_4427_);
lean_dec(v_a_4425_);
v___x_4428_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4427_, v_fst_4426_, v_x_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
return v___x_4428_;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_x_4414_);
v_a_4429_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4424_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4424_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_4441_; lean_object* v___x_4442_; 
lean_dec_ref(v_00_u03c3_4412_);
v_fvarId_4441_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_fvarId_4441_);
lean_dec_ref_known(v_x_4413_, 1);
v___x_4442_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4441_, v_a_4415_, v_a_4417_, v_a_4418_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4445_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4444_, v_a_4443_, v_x_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
return v___x_4445_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_x_4414_);
v_a_4446_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4442_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4442_);
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
case 2:
{
lean_object* v_mvarId_4454_; lean_object* v___x_4455_; 
lean_dec_ref(v_00_u03c3_4412_);
v_mvarId_4454_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_mvarId_4454_);
lean_dec_ref_known(v_x_4413_, 1);
v___x_4455_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4454_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4458_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4457_, v_a_4456_, v_x_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
return v___x_4458_;
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec(v_x_4414_);
v_a_4459_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4455_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
case 5:
{
lean_object* v_fn_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_fn_4467_ = lean_ctor_get(v_x_4413_, 0);
lean_inc_ref(v_fn_4467_);
lean_dec_ref_known(v_x_4413_, 2);
v___x_4468_ = lean_unsigned_to_nat(1u);
v___x_4469_ = lean_nat_add(v_x_4414_, v___x_4468_);
lean_dec(v_x_4414_);
v_x_4413_ = v_fn_4467_;
v_x_4414_ = v___x_4469_;
goto _start;
}
case 10:
{
lean_object* v_expr_4471_; 
v_expr_4471_ = lean_ctor_get(v_x_4413_, 1);
lean_inc_ref(v_expr_4471_);
lean_dec_ref_known(v_x_4413_, 2);
v_x_4413_ = v_expr_4471_;
goto _start;
}
case 8:
{
lean_object* v_body_4473_; 
v_body_4473_ = lean_ctor_get(v_x_4413_, 3);
lean_inc_ref(v_body_4473_);
lean_dec_ref_known(v_x_4413_, 4);
v_x_4413_ = v_body_4473_;
goto _start;
}
case 6:
{
lean_object* v_body_4475_; lean_object* v_zero_4476_; uint8_t v_isZero_4477_; 
v_body_4475_ = lean_ctor_get(v_x_4413_, 2);
lean_inc_ref(v_body_4475_);
lean_dec_ref_known(v_x_4413_, 3);
v_zero_4476_ = lean_unsigned_to_nat(0u);
v_isZero_4477_ = lean_nat_dec_eq(v_x_4414_, v_zero_4476_);
if (v_isZero_4477_ == 1)
{
uint8_t v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
lean_dec_ref(v_body_4475_);
lean_dec(v_x_4414_);
lean_dec_ref(v_00_u03c3_4412_);
v___x_4478_ = 0;
v___x_4479_ = lean_box(v___x_4478_);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
else
{
lean_object* v_one_4481_; lean_object* v_n_4482_; 
v_one_4481_ = lean_unsigned_to_nat(1u);
v_n_4482_ = lean_nat_sub(v_x_4414_, v_one_4481_);
lean_dec(v_x_4414_);
v_x_4413_ = v_body_4475_;
v_x_4414_ = v_n_4482_;
goto _start;
}
}
default: 
{
uint8_t v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
lean_dec(v_x_4414_);
lean_dec_ref(v_x_4413_);
lean_dec_ref(v_00_u03c3_4412_);
v___x_4484_ = 2;
v___x_4485_ = lean_box(v___x_4484_);
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
return v___x_4486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_00_u03c3_4487_, lean_object* v_x_4488_, lean_object* v_x_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4487_, v_x_4488_, v_x_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object* v_00_u03c3_4496_, lean_object* v_x_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
switch(lean_obj_tag(v_x_4497_))
{
case 1:
{
lean_object* v_fvarId_4503_; lean_object* v___x_4504_; 
lean_dec_ref(v_00_u03c3_4496_);
v_fvarId_4503_ = lean_ctor_get(v_x_4497_, 0);
lean_inc(v_fvarId_4503_);
lean_dec_ref_known(v_x_4497_, 1);
v___x_4504_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4503_, v_a_4498_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4507_ = lean_unsigned_to_nat(0u);
v___x_4508_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4506_, v_a_4505_, v___x_4507_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4508_;
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
v_a_4509_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4504_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4504_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4517_; lean_object* v___x_4518_; 
lean_dec_ref(v_00_u03c3_4496_);
v_mvarId_4517_ = lean_ctor_get(v_x_4497_, 0);
lean_inc(v_mvarId_4517_);
lean_dec_ref_known(v_x_4497_, 1);
v___x_4518_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4517_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4518_, 1);
v___x_4520_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4521_ = lean_unsigned_to_nat(0u);
v___x_4522_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4520_, v_a_4519_, v___x_4521_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4522_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
v_a_4523_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4518_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4518_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
case 3:
{
uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
lean_dec_ref_known(v_x_4497_, 1);
lean_dec_ref(v_00_u03c3_4496_);
v___x_4531_ = 0;
v___x_4532_ = lean_box(v___x_4531_);
v___x_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
return v___x_4533_;
}
case 4:
{
lean_object* v_declName_4534_; lean_object* v_us_4535_; lean_object* v___y_4537_; lean_object* v_paramNames_4552_; uint8_t v___x_4553_; 
v_declName_4534_ = lean_ctor_get(v_x_4497_, 0);
lean_inc(v_declName_4534_);
v_us_4535_ = lean_ctor_get(v_x_4497_, 1);
lean_inc(v_us_4535_);
lean_dec_ref_known(v_x_4497_, 2);
v_paramNames_4552_ = lean_ctor_get(v_00_u03c3_4496_, 0);
v___x_4553_ = l_List_isEmpty___redArg(v_paramNames_4552_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = lean_box(0);
v___x_4555_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4496_, v_us_4535_, v___x_4554_);
v___y_4537_ = v___x_4555_;
goto v___jp_4536_;
}
else
{
lean_dec_ref(v_00_u03c3_4496_);
v___y_4537_ = v_us_4535_;
goto v___jp_4536_;
}
v___jp_4536_:
{
lean_object* v___x_4538_; 
v___x_4538_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4534_, v___y_4537_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v_fst_4540_; lean_object* v_snd_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v_fst_4540_ = lean_ctor_get(v_a_4539_, 0);
lean_inc(v_fst_4540_);
v_snd_4541_ = lean_ctor_get(v_a_4539_, 1);
lean_inc(v_snd_4541_);
lean_dec(v_a_4539_);
v___x_4542_ = lean_unsigned_to_nat(0u);
v___x_4543_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4541_, v_fst_4540_, v___x_4542_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4543_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_a_4544_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4538_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4538_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v_fn_4556_ = lean_ctor_get(v_x_4497_, 0);
lean_inc_ref(v_fn_4556_);
lean_dec_ref_known(v_x_4497_, 2);
v___x_4557_ = lean_unsigned_to_nat(1u);
v___x_4558_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4496_, v_fn_4556_, v___x_4557_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4558_;
}
case 6:
{
uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
lean_dec_ref_known(v_x_4497_, 3);
lean_dec_ref(v_00_u03c3_4496_);
v___x_4559_ = 0;
v___x_4560_ = lean_box(v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
case 7:
{
lean_object* v_body_4562_; 
v_body_4562_ = lean_ctor_get(v_x_4497_, 2);
lean_inc_ref(v_body_4562_);
lean_dec_ref_known(v_x_4497_, 3);
v_x_4497_ = v_body_4562_;
goto _start;
}
case 8:
{
lean_object* v_body_4564_; 
v_body_4564_ = lean_ctor_get(v_x_4497_, 3);
lean_inc_ref(v_body_4564_);
lean_dec_ref_known(v_x_4497_, 4);
v_x_4497_ = v_body_4564_;
goto _start;
}
case 9:
{
uint8_t v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
lean_dec_ref_known(v_x_4497_, 1);
lean_dec_ref(v_00_u03c3_4496_);
v___x_4566_ = 0;
v___x_4567_ = lean_box(v___x_4566_);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
case 10:
{
lean_object* v_expr_4569_; 
v_expr_4569_ = lean_ctor_get(v_x_4497_, 1);
lean_inc_ref(v_expr_4569_);
lean_dec_ref_known(v_x_4497_, 2);
v_x_4497_ = v_expr_4569_;
goto _start;
}
default: 
{
uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec_ref(v_x_4497_);
lean_dec_ref(v_00_u03c3_4496_);
v___x_4571_ = 2;
v___x_4572_ = lean_box(v___x_4571_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object* v_00_u03c3_4574_, lean_object* v_x_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4574_, v_x_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_e_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4589_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v___x_4588_, v_e_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_e_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Meta_isPropQuick(v_e_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v___x_4603_; 
lean_inc_ref(v_e_4597_);
v___x_4603_ = l_Lean_Meta_isPropQuick(v_e_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4660_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4606_ = v___x_4603_;
v_isShared_4607_ = v_isSharedCheck_4660_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4603_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4660_;
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
v___x_4621_ = l_Lean_Meta_whnfD(v_a_4620_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4643_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4643_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4643_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
if (lean_obj_tag(v_a_4622_) == 3)
{
lean_object* v_u_4626_; lean_object* v___x_4627_; lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4637_; 
lean_del_object(v___x_4624_);
v_u_4626_ = lean_ctor_get(v_a_4622_, 0);
lean_inc(v_u_4626_);
lean_dec_ref_known(v_a_4622_, 1);
v___x_4627_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4626_, v_a_4599_);
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4630_ = v___x_4627_;
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4627_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
uint8_t v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4632_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4628_);
lean_dec(v_a_4628_);
v___x_4633_ = lean_box(v___x_4632_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4633_);
v___x_4635_ = v___x_4630_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
else
{
uint8_t v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
lean_dec(v_a_4622_);
v___x_4638_ = 0;
v___x_4639_ = lean_box(v___x_4638_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4639_);
v___x_4641_ = v___x_4624_;
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
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
v_a_4644_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4621_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4621_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
v_a_4652_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4619_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4619_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
lean_dec_ref(v_e_4597_);
v_a_4661_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4603_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4603_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_Meta_isProp(v_e_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4676_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_obj_tag_nat(v_x_4676_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4678_);
lean_dec(v_x_4678_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4680_, lean_object* v_k_4681_){
_start:
{
if (lean_obj_tag(v_t_4680_) == 3)
{
lean_object* v_idx_4682_; lean_object* v_numArgs_4683_; lean_object* v___x_4684_; 
v_idx_4682_ = lean_ctor_get(v_t_4680_, 0);
lean_inc(v_idx_4682_);
v_numArgs_4683_ = lean_ctor_get(v_t_4680_, 1);
lean_inc(v_numArgs_4683_);
lean_dec_ref_known(v_t_4680_, 2);
v___x_4684_ = lean_apply_2(v_k_4681_, v_idx_4682_, v_numArgs_4683_);
return v___x_4684_;
}
else
{
lean_dec(v_t_4680_);
return v_k_4681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4685_, lean_object* v_ctorIdx_4686_, lean_object* v_t_4687_, lean_object* v_h_4688_, lean_object* v_k_4689_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4687_, v_k_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4691_, lean_object* v_ctorIdx_4692_, lean_object* v_t_4693_, lean_object* v_h_4694_, lean_object* v_k_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4691_, v_ctorIdx_4692_, v_t_4693_, v_h_4694_, v_k_4695_);
lean_dec(v_ctorIdx_4692_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4697_, lean_object* v_false_4698_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4697_, v_false_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4700_, lean_object* v_t_4701_, lean_object* v_h_4702_, lean_object* v_false_4703_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4701_, v_false_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4705_, lean_object* v_true_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4705_, v_true_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4708_, lean_object* v_t_4709_, lean_object* v_h_4710_, lean_object* v_true_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4709_, v_true_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4713_, lean_object* v_undef_4714_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4713_, v_undef_4714_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4716_, lean_object* v_t_4717_, lean_object* v_h_4718_, lean_object* v_undef_4719_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4717_, v_undef_4719_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4721_, lean_object* v_bvar_4722_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4721_, v_bvar_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4724_, lean_object* v_t_4725_, lean_object* v_h_4726_, lean_object* v_bvar_4727_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4725_, v_bvar_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4729_){
_start:
{
switch(v_x_4729_)
{
case 0:
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_box(0);
return v___x_4730_;
}
case 1:
{
lean_object* v___x_4731_; 
v___x_4731_ = lean_box(1);
return v___x_4731_;
}
default: 
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_box(2);
return v___x_4732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4733_){
_start:
{
uint8_t v_x_25__boxed_4734_; lean_object* v_res_4735_; 
v_x_25__boxed_4734_ = lean_unbox(v_x_4733_);
v_res_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4734_);
return v_res_4735_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4736_){
_start:
{
switch(lean_obj_tag(v_x_4736_))
{
case 0:
{
uint8_t v___x_4737_; 
v___x_4737_ = 0;
return v___x_4737_;
}
case 1:
{
uint8_t v___x_4738_; 
v___x_4738_ = 1;
return v___x_4738_;
}
default: 
{
uint8_t v___x_4739_; 
v___x_4739_ = 2;
return v___x_4739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4740_){
_start:
{
uint8_t v_res_4741_; lean_object* v_r_4742_; 
v_res_4741_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4740_);
lean_dec(v_x_4740_);
v_r_4742_ = lean_box(v_res_4741_);
return v_r_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_00_u03c3_4744_, lean_object* v_e_4745_, lean_object* v_numArgs_4746_){
_start:
{
lean_object* v___y_4748_; 
switch(lean_obj_tag(v_e_4745_))
{
case 3:
{
lean_object* v_u_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v_u_4754_ = lean_ctor_get(v_e_4745_, 0);
lean_inc(v_u_4754_);
lean_dec_ref_known(v_e_4745_, 1);
v___x_4755_ = lean_unsigned_to_nat(0u);
v___x_4756_ = lean_nat_dec_eq(v_numArgs_4746_, v___x_4755_);
lean_dec(v_numArgs_4746_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; 
lean_dec(v_u_4754_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4757_ = lean_box(2);
return v___x_4757_;
}
else
{
lean_object* v_paramNames_4758_; lean_object* v_lvls_4759_; uint8_t v___x_4760_; 
v_paramNames_4758_ = lean_ctor_get(v_00_u03c3_4744_, 0);
lean_inc(v_paramNames_4758_);
v_lvls_4759_ = lean_ctor_get(v_00_u03c3_4744_, 1);
lean_inc(v_lvls_4759_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4760_ = l_List_isEmpty___redArg(v_paramNames_4758_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Lean_Level_instantiateParams(v_u_4754_, v_paramNames_4758_, v_lvls_4759_);
v___y_4748_ = v___x_4761_;
goto v___jp_4747_;
}
else
{
lean_dec(v_lvls_4759_);
lean_dec(v_paramNames_4758_);
v___y_4748_ = v_u_4754_;
goto v___jp_4747_;
}
}
}
case 7:
{
lean_object* v_body_4762_; lean_object* v_zero_4763_; uint8_t v_isZero_4764_; 
v_body_4762_ = lean_ctor_get(v_e_4745_, 2);
lean_inc_ref(v_body_4762_);
lean_dec_ref_known(v_e_4745_, 3);
v_zero_4763_ = lean_unsigned_to_nat(0u);
v_isZero_4764_ = lean_nat_dec_eq(v_numArgs_4746_, v_zero_4763_);
if (v_isZero_4764_ == 0)
{
lean_object* v_one_4765_; lean_object* v_n_4766_; 
v_one_4765_ = lean_unsigned_to_nat(1u);
v_n_4766_ = lean_nat_sub(v_numArgs_4746_, v_one_4765_);
lean_dec(v_numArgs_4746_);
v_e_4745_ = v_body_4762_;
v_numArgs_4746_ = v_n_4766_;
goto _start;
}
else
{
lean_object* v___x_4768_; 
lean_dec_ref(v_body_4762_);
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4768_ = lean_box(2);
return v___x_4768_;
}
}
case 10:
{
lean_object* v_expr_4769_; 
v_expr_4769_ = lean_ctor_get(v_e_4745_, 1);
lean_inc_ref(v_expr_4769_);
lean_dec_ref_known(v_e_4745_, 2);
v_e_4745_ = v_expr_4769_;
goto _start;
}
case 5:
{
lean_object* v_fn_4771_; 
v_fn_4771_ = lean_ctor_get(v_e_4745_, 0);
if (lean_obj_tag(v_fn_4771_) == 4)
{
lean_object* v_declName_4772_; 
v_declName_4772_ = lean_ctor_get(v_fn_4771_, 0);
lean_inc(v_declName_4772_);
if (lean_obj_tag(v_declName_4772_) == 1)
{
lean_object* v_pre_4773_; 
v_pre_4773_ = lean_ctor_get(v_declName_4772_, 0);
if (lean_obj_tag(v_pre_4773_) == 0)
{
lean_object* v_arg_4774_; lean_object* v_str_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_arg_4774_ = lean_ctor_get(v_e_4745_, 1);
lean_inc_ref(v_arg_4774_);
lean_dec_ref_known(v_e_4745_, 2);
v_str_4775_ = lean_ctor_get(v_declName_4772_, 1);
lean_inc_ref(v_str_4775_);
lean_dec_ref_known(v_declName_4772_, 2);
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4777_ = lean_string_dec_eq(v_str_4775_, v___x_4776_);
lean_dec_ref(v_str_4775_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; 
lean_dec_ref(v_arg_4774_);
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4778_ = lean_box(2);
return v___x_4778_;
}
else
{
v_e_4745_ = v_arg_4774_;
goto _start;
}
}
else
{
lean_object* v___x_4780_; 
lean_dec_ref_known(v_declName_4772_, 2);
lean_dec_ref_known(v_e_4745_, 2);
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4780_ = lean_box(2);
return v___x_4780_;
}
}
else
{
lean_object* v___x_4781_; 
lean_dec(v_declName_4772_);
lean_dec_ref_known(v_e_4745_, 2);
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4781_ = lean_box(2);
return v___x_4781_;
}
}
else
{
lean_object* v___x_4782_; 
lean_dec_ref_known(v_e_4745_, 2);
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4782_ = lean_box(2);
return v___x_4782_;
}
}
default: 
{
lean_object* v___x_4783_; 
lean_dec(v_numArgs_4746_);
lean_dec_ref(v_e_4745_);
lean_dec_ref(v_00_u03c3_4744_);
v___x_4783_ = lean_box(2);
return v___x_4783_;
}
}
v___jp_4747_:
{
uint8_t v___x_4749_; 
v___x_4749_ = l_Lean_Level_isNeverZero(v___y_4748_);
if (v___x_4749_ == 0)
{
uint8_t v___x_4750_; 
v___x_4750_ = l_Lean_Level_isZero(v___y_4748_);
lean_dec(v___y_4748_);
if (v___x_4750_ == 0)
{
lean_object* v___x_4751_; 
v___x_4751_ = lean_box(2);
return v___x_4751_;
}
else
{
lean_object* v___x_4752_; 
v___x_4752_ = lean_box(1);
return v___x_4752_;
}
}
else
{
lean_object* v___x_4753_; 
lean_dec(v___y_4748_);
v___x_4753_ = lean_box(0);
return v___x_4753_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_00_u03c3_4784_, lean_object* v_r_4785_, lean_object* v_binderType_4786_){
_start:
{
if (lean_obj_tag(v_r_4785_) == 3)
{
lean_object* v_idx_4787_; lean_object* v_numArgs_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4800_; 
v_idx_4787_ = lean_ctor_get(v_r_4785_, 0);
v_numArgs_4788_ = lean_ctor_get(v_r_4785_, 1);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_r_4785_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4790_ = v_r_4785_;
v_isShared_4791_ = v_isSharedCheck_4800_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_numArgs_4788_);
lean_inc(v_idx_4787_);
lean_dec(v_r_4785_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4800_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v_zero_4792_; uint8_t v_isZero_4793_; 
v_zero_4792_ = lean_unsigned_to_nat(0u);
v_isZero_4793_ = lean_nat_dec_eq(v_idx_4787_, v_zero_4792_);
if (v_isZero_4793_ == 1)
{
lean_object* v___x_4794_; 
lean_del_object(v___x_4790_);
lean_dec(v_idx_4787_);
v___x_4794_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_00_u03c3_4784_, v_binderType_4786_, v_numArgs_4788_);
return v___x_4794_;
}
else
{
lean_object* v_one_4795_; lean_object* v_n_4796_; lean_object* v___x_4798_; 
lean_dec_ref(v_binderType_4786_);
lean_dec_ref(v_00_u03c3_4784_);
v_one_4795_ = lean_unsigned_to_nat(1u);
v_n_4796_ = lean_nat_sub(v_idx_4787_, v_one_4795_);
lean_dec(v_idx_4787_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v_n_4796_);
v___x_4798_ = v___x_4790_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_n_4796_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_numArgs_4788_);
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
else
{
lean_dec_ref(v_binderType_4786_);
lean_dec_ref(v_00_u03c3_4784_);
return v_r_4785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_00_u03c3_4801_, lean_object* v_x_4802_, lean_object* v_x_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v_type_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; 
switch(lean_obj_tag(v_x_4802_))
{
case 7:
{
lean_object* v_binderType_4842_; lean_object* v_body_4843_; lean_object* v_zero_4844_; uint8_t v_isZero_4845_; 
v_binderType_4842_ = lean_ctor_get(v_x_4802_, 1);
v_body_4843_ = lean_ctor_get(v_x_4802_, 2);
v_zero_4844_ = lean_unsigned_to_nat(0u);
v_isZero_4845_ = lean_nat_dec_eq(v_x_4803_, v_zero_4844_);
if (v_isZero_4845_ == 1)
{
v_type_4810_ = v_x_4802_;
v___y_4811_ = v_a_4804_;
v___y_4812_ = v_a_4805_;
v___y_4813_ = v_a_4806_;
v___y_4814_ = v_a_4807_;
goto v___jp_4809_;
}
else
{
lean_object* v_one_4846_; lean_object* v_n_4847_; lean_object* v___x_4848_; 
lean_inc_ref(v_body_4843_);
lean_inc_ref(v_binderType_4842_);
lean_dec_ref_known(v_x_4802_, 3);
v_one_4846_ = lean_unsigned_to_nat(1u);
v_n_4847_ = lean_nat_sub(v_x_4803_, v_one_4846_);
lean_inc_ref(v_00_u03c3_4801_);
v___x_4848_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4801_, v_body_4843_, v_n_4847_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_n_4847_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4857_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4853_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4801_, v_a_4849_, v_binderType_4842_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4853_);
v___x_4855_ = v___x_4851_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
else
{
lean_dec_ref(v_binderType_4842_);
lean_dec_ref(v_00_u03c3_4801_);
return v___x_4848_;
}
}
}
case 8:
{
lean_object* v_type_4858_; lean_object* v_body_4859_; lean_object* v___x_4860_; 
v_type_4858_ = lean_ctor_get(v_x_4802_, 1);
lean_inc_ref(v_type_4858_);
v_body_4859_ = lean_ctor_get(v_x_4802_, 3);
lean_inc_ref(v_body_4859_);
lean_dec_ref_known(v_x_4802_, 4);
lean_inc_ref(v_00_u03c3_4801_);
v___x_4860_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4801_, v_body_4859_, v_x_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4869_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4863_ = v___x_4860_;
v_isShared_4864_ = v_isSharedCheck_4869_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4860_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4869_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4865_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4801_, v_a_4861_, v_type_4858_);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 0, v___x_4865_);
v___x_4867_ = v___x_4863_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
else
{
lean_dec_ref(v_type_4858_);
lean_dec_ref(v_00_u03c3_4801_);
return v___x_4860_;
}
}
case 10:
{
lean_object* v_expr_4870_; 
v_expr_4870_ = lean_ctor_get(v_x_4802_, 1);
lean_inc_ref(v_expr_4870_);
lean_dec_ref_known(v_x_4802_, 2);
v_x_4802_ = v_expr_4870_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
lean_dec_ref(v_00_u03c3_4801_);
v_deBruijnIndex_4872_ = lean_ctor_get(v_x_4802_, 0);
lean_inc(v_deBruijnIndex_4872_);
lean_dec_ref_known(v_x_4802_, 1);
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = lean_nat_dec_eq(v_x_4803_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_dec(v_deBruijnIndex_4872_);
goto v___jp_4839_;
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4875_, 0, v_deBruijnIndex_4872_);
lean_ctor_set(v___x_4875_, 1, v___x_4873_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
return v___x_4876_;
}
}
default: 
{
lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4877_ = lean_unsigned_to_nat(0u);
v___x_4878_ = lean_nat_dec_eq(v_x_4803_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_dec_ref(v_x_4802_);
lean_dec_ref(v_00_u03c3_4801_);
goto v___jp_4839_;
}
else
{
v_type_4810_ = v_x_4802_;
v___y_4811_ = v_a_4804_;
v___y_4812_ = v_a_4805_;
v___y_4813_ = v_a_4806_;
v___y_4814_ = v_a_4807_;
goto v___jp_4809_;
}
}
}
v___jp_4809_:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Expr_getAppFn(v_type_4810_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_deBruijnIndex_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
lean_dec_ref(v_00_u03c3_4801_);
v_deBruijnIndex_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_deBruijnIndex_4816_);
lean_dec_ref_known(v___x_4815_, 1);
v___x_4817_ = l_Lean_Expr_getAppNumArgs(v_type_4810_);
lean_dec_ref(v_type_4810_);
v___x_4818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4818_, 0, v_deBruijnIndex_4816_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
return v___x_4819_;
}
else
{
lean_object* v___x_4820_; 
lean_dec_ref(v___x_4815_);
v___x_4820_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4801_, v_type_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4830_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4823_ = v___x_4820_;
v_isShared_4824_ = v_isSharedCheck_4830_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4820_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4830_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
uint8_t v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4825_ = lean_unbox(v_a_4821_);
lean_dec(v_a_4821_);
v___x_4826_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4825_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v___x_4826_);
v___x_4828_ = v___x_4823_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4820_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4820_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
}
v___jp_4839_:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = lean_box(2);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_00_u03c3_4879_, lean_object* v_x_4880_, lean_object* v_x_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4879_, v_x_4880_, v_x_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_x_4881_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_00_u03c3_4888_, lean_object* v_e_4889_, lean_object* v_n_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4888_, v_e_4889_, v_n_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4906_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
uint8_t v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4901_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4897_);
lean_dec(v_a_4897_);
v___x_4902_ = lean_box(v___x_4901_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4902_);
v___x_4904_ = v___x_4899_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
v_a_4907_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4896_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4896_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_00_u03c3_4915_, lean_object* v_e_4916_, lean_object* v_n_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_00_u03c3_4915_, v_e_4916_, v_n_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
lean_dec(v_a_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v_n_4917_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_){
_start:
{
switch(lean_obj_tag(v_x_4924_))
{
case 1:
{
lean_object* v_fvarId_4930_; lean_object* v___x_4931_; 
v_fvarId_4930_ = lean_ctor_get(v_x_4924_, 0);
lean_inc(v_fvarId_4930_);
lean_dec_ref_known(v_x_4924_, 1);
v___x_4931_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4930_, v_a_4925_, v_a_4927_, v_a_4928_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
v___x_4933_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4934_ = lean_unsigned_to_nat(0u);
v___x_4935_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4933_, v_a_4932_, v___x_4934_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
return v___x_4935_;
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4936_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4931_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4931_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
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
case 2:
{
lean_object* v_mvarId_4944_; lean_object* v___x_4945_; 
v_mvarId_4944_ = lean_ctor_get(v_x_4924_, 0);
lean_inc(v_mvarId_4944_);
lean_dec_ref_known(v_x_4924_, 1);
v___x_4945_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4944_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___x_4945_, 1);
v___x_4947_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4948_ = lean_unsigned_to_nat(0u);
v___x_4949_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4947_, v_a_4946_, v___x_4948_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
return v___x_4949_;
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4945_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4945_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
case 3:
{
uint8_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec_ref_known(v_x_4924_, 1);
v___x_4958_ = 0;
v___x_4959_ = lean_box(v___x_4958_);
v___x_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
return v___x_4960_;
}
case 4:
{
lean_object* v_declName_4961_; lean_object* v_us_4962_; lean_object* v___x_4963_; 
v_declName_4961_ = lean_ctor_get(v_x_4924_, 0);
lean_inc(v_declName_4961_);
v_us_4962_ = lean_ctor_get(v_x_4924_, 1);
lean_inc(v_us_4962_);
lean_dec_ref_known(v_x_4924_, 2);
v___x_4963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4961_, v_us_4962_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v_fst_4965_; lean_object* v_snd_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v_fst_4965_ = lean_ctor_get(v_a_4964_, 0);
lean_inc(v_fst_4965_);
v_snd_4966_ = lean_ctor_get(v_a_4964_, 1);
lean_inc(v_snd_4966_);
lean_dec(v_a_4964_);
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4966_, v_fst_4965_, v___x_4967_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
return v___x_4968_;
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
v_a_4969_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4963_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4963_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
case 5:
{
lean_object* v_fn_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v_fn_4977_ = lean_ctor_get(v_x_4924_, 0);
lean_inc_ref(v_fn_4977_);
lean_dec_ref_known(v_x_4924_, 2);
v___x_4978_ = lean_unsigned_to_nat(1u);
v___x_4979_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4977_, v___x_4978_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_);
return v___x_4979_;
}
case 6:
{
lean_object* v_body_4980_; 
v_body_4980_ = lean_ctor_get(v_x_4924_, 2);
lean_inc_ref(v_body_4980_);
lean_dec_ref_known(v_x_4924_, 3);
v_x_4924_ = v_body_4980_;
goto _start;
}
case 7:
{
uint8_t v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec_ref_known(v_x_4924_, 3);
v___x_4982_ = 0;
v___x_4983_ = lean_box(v___x_4982_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
return v___x_4984_;
}
case 8:
{
lean_object* v_body_4985_; 
v_body_4985_ = lean_ctor_get(v_x_4924_, 3);
lean_inc_ref(v_body_4985_);
lean_dec_ref_known(v_x_4924_, 4);
v_x_4924_ = v_body_4985_;
goto _start;
}
case 9:
{
uint8_t v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
lean_dec_ref_known(v_x_4924_, 1);
v___x_4987_ = 0;
v___x_4988_ = lean_box(v___x_4987_);
v___x_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4988_);
return v___x_4989_;
}
case 10:
{
lean_object* v_expr_4990_; 
v_expr_4990_ = lean_ctor_get(v_x_4924_, 1);
lean_inc_ref(v_expr_4990_);
lean_dec_ref_known(v_x_4924_, 2);
v_x_4924_ = v_expr_4990_;
goto _start;
}
default: 
{
uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_dec_ref(v_x_4924_);
v___x_4992_ = 2;
v___x_4993_ = lean_box(v___x_4992_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4995_, lean_object* v_x_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
switch(lean_obj_tag(v_x_4995_))
{
case 4:
{
lean_object* v_declName_5002_; lean_object* v_us_5003_; lean_object* v___x_5004_; 
v_declName_5002_ = lean_ctor_get(v_x_4995_, 0);
lean_inc(v_declName_5002_);
v_us_5003_ = lean_ctor_get(v_x_4995_, 1);
lean_inc(v_us_5003_);
lean_dec_ref_known(v_x_4995_, 2);
v___x_5004_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5002_, v_us_5003_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v_fst_5006_; lean_object* v_snd_5007_; lean_object* v___x_5008_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_a_5005_);
lean_dec_ref_known(v___x_5004_, 1);
v_fst_5006_ = lean_ctor_get(v_a_5005_, 0);
lean_inc(v_fst_5006_);
v_snd_5007_ = lean_ctor_get(v_a_5005_, 1);
lean_inc(v_snd_5007_);
lean_dec(v_a_5005_);
v___x_5008_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_5007_, v_fst_5006_, v_x_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_x_4996_);
return v___x_5008_;
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
lean_dec(v_x_4996_);
v_a_5009_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_5004_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5004_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
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
case 1:
{
lean_object* v_fvarId_5017_; lean_object* v___x_5018_; 
v_fvarId_5017_ = lean_ctor_get(v_x_4995_, 0);
lean_inc(v_fvarId_5017_);
lean_dec_ref_known(v_x_4995_, 1);
v___x_5018_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5017_, v_a_4997_, v_a_4999_, v_a_5000_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5019_);
lean_dec_ref_known(v___x_5018_, 1);
v___x_5020_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5021_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5020_, v_a_5019_, v_x_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_x_4996_);
return v___x_5021_;
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_dec(v_x_4996_);
v_a_5022_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5018_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5018_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5030_; lean_object* v___x_5031_; 
v_mvarId_5030_ = lean_ctor_get(v_x_4995_, 0);
lean_inc(v_mvarId_5030_);
lean_dec_ref_known(v_x_4995_, 1);
v___x_5031_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5030_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5033_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5034_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5033_, v_a_5032_, v_x_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec(v_x_4996_);
return v___x_5034_;
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
lean_dec(v_x_4996_);
v_a_5035_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5031_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5031_);
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
case 5:
{
lean_object* v_fn_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v_fn_5043_ = lean_ctor_get(v_x_4995_, 0);
lean_inc_ref(v_fn_5043_);
lean_dec_ref_known(v_x_4995_, 2);
v___x_5044_ = lean_unsigned_to_nat(1u);
v___x_5045_ = lean_nat_add(v_x_4996_, v___x_5044_);
lean_dec(v_x_4996_);
v_x_4995_ = v_fn_5043_;
v_x_4996_ = v___x_5045_;
goto _start;
}
case 10:
{
lean_object* v_expr_5047_; 
v_expr_5047_ = lean_ctor_get(v_x_4995_, 1);
lean_inc_ref(v_expr_5047_);
lean_dec_ref_known(v_x_4995_, 2);
v_x_4995_ = v_expr_5047_;
goto _start;
}
case 8:
{
lean_object* v_body_5049_; 
v_body_5049_ = lean_ctor_get(v_x_4995_, 3);
lean_inc_ref(v_body_5049_);
lean_dec_ref_known(v_x_4995_, 4);
v_x_4995_ = v_body_5049_;
goto _start;
}
case 6:
{
lean_object* v_body_5051_; lean_object* v_zero_5052_; uint8_t v_isZero_5053_; 
v_body_5051_ = lean_ctor_get(v_x_4995_, 2);
lean_inc_ref(v_body_5051_);
lean_dec_ref_known(v_x_4995_, 3);
v_zero_5052_ = lean_unsigned_to_nat(0u);
v_isZero_5053_ = lean_nat_dec_eq(v_x_4996_, v_zero_5052_);
if (v_isZero_5053_ == 1)
{
lean_object* v___x_5054_; 
lean_dec(v_x_4996_);
v___x_5054_ = l_Lean_Meta_isProofQuick(v_body_5051_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5054_;
}
else
{
lean_object* v_one_5055_; lean_object* v_n_5056_; 
v_one_5055_ = lean_unsigned_to_nat(1u);
v_n_5056_ = lean_nat_sub(v_x_4996_, v_one_5055_);
lean_dec(v_x_4996_);
v_x_4995_ = v_body_5051_;
v_x_4996_ = v_n_5056_;
goto _start;
}
}
default: 
{
uint8_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_dec(v_x_4996_);
lean_dec_ref(v_x_4995_);
v___x_5058_ = 2;
v___x_5059_ = lean_box(v___x_5058_);
v___x_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5059_);
return v___x_5060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_5061_, lean_object* v_x_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_5061_, v_x_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l_Lean_Meta_isProofQuick(v_x_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_);
lean_dec(v_a_5073_);
lean_dec_ref(v_a_5072_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
return v_res_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___x_5082_; 
lean_inc_ref(v_e_5076_);
v___x_5082_ = l_Lean_Meta_isProofQuick(v_e_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5109_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5085_ = v___x_5082_;
v_isShared_5086_ = v_isSharedCheck_5109_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5082_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5109_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
uint8_t v___x_5087_; 
v___x_5087_ = lean_unbox(v_a_5083_);
lean_dec(v_a_5083_);
switch(v___x_5087_)
{
case 0:
{
uint8_t v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5091_; 
lean_dec_ref(v_e_5076_);
v___x_5088_ = 0;
v___x_5089_ = lean_box(v___x_5088_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 0, v___x_5089_);
v___x_5091_ = v___x_5085_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
case 1:
{
uint8_t v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5096_; 
lean_dec_ref(v_e_5076_);
v___x_5093_ = 1;
v___x_5094_ = lean_box(v___x_5093_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 0, v___x_5094_);
v___x_5096_ = v___x_5085_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
default: 
{
lean_object* v___x_5098_; 
lean_del_object(v___x_5085_);
lean_inc(v_a_5080_);
lean_inc_ref(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5098_ = lean_infer_type(v_e_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5100_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v___x_5100_ = l_Lean_Meta_isProp(v_a_5099_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
return v___x_5100_;
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
v_a_5101_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5098_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5098_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec_ref(v_e_5076_);
v_a_5110_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5082_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5082_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_isProof(v_e_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_5125_, lean_object* v_x_5126_){
_start:
{
switch(lean_obj_tag(v_x_5125_))
{
case 3:
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = lean_unsigned_to_nat(0u);
v___x_5133_ = lean_nat_dec_eq(v_x_5126_, v___x_5132_);
lean_dec(v_x_5126_);
if (v___x_5133_ == 0)
{
goto v___jp_5128_;
}
else
{
uint8_t v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5134_ = 1;
v___x_5135_ = lean_box(v___x_5134_);
v___x_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5135_);
return v___x_5136_;
}
}
case 7:
{
lean_object* v_body_5137_; lean_object* v_zero_5138_; uint8_t v_isZero_5139_; 
v_body_5137_ = lean_ctor_get(v_x_5125_, 2);
v_zero_5138_ = lean_unsigned_to_nat(0u);
v_isZero_5139_ = lean_nat_dec_eq(v_x_5126_, v_zero_5138_);
if (v_isZero_5139_ == 1)
{
uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
lean_dec(v_x_5126_);
v___x_5140_ = 0;
v___x_5141_ = lean_box(v___x_5140_);
v___x_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
return v___x_5142_;
}
else
{
lean_object* v_one_5143_; lean_object* v_n_5144_; 
v_one_5143_ = lean_unsigned_to_nat(1u);
v_n_5144_ = lean_nat_sub(v_x_5126_, v_one_5143_);
lean_dec(v_x_5126_);
v_x_5125_ = v_body_5137_;
v_x_5126_ = v_n_5144_;
goto _start;
}
}
case 8:
{
lean_object* v_body_5146_; 
v_body_5146_ = lean_ctor_get(v_x_5125_, 3);
v_x_5125_ = v_body_5146_;
goto _start;
}
case 10:
{
lean_object* v_expr_5148_; 
v_expr_5148_ = lean_ctor_get(v_x_5125_, 1);
v_x_5125_ = v_expr_5148_;
goto _start;
}
default: 
{
lean_dec(v_x_5126_);
goto v___jp_5128_;
}
}
v___jp_5128_:
{
uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5129_ = 2;
v___x_5130_ = lean_box(v___x_5129_);
v___x_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5130_);
return v___x_5131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_5150_, lean_object* v_x_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5150_, v_x_5151_);
lean_dec_ref(v_x_5150_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_5154_, lean_object* v_x_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5154_, v_x_5155_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_5162_, lean_object* v_x_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_5162_, v_x_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec_ref(v_x_5162_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_5170_, lean_object* v_x_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
switch(lean_obj_tag(v_x_5170_))
{
case 4:
{
lean_object* v_declName_5177_; lean_object* v_us_5178_; lean_object* v___x_5179_; 
v_declName_5177_ = lean_ctor_get(v_x_5170_, 0);
lean_inc(v_declName_5177_);
v_us_5178_ = lean_ctor_get(v_x_5170_, 1);
lean_inc(v_us_5178_);
lean_dec_ref_known(v_x_5170_, 2);
v___x_5179_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5177_, v_us_5178_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; lean_object* v_fst_5181_; lean_object* v___x_5182_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref_known(v___x_5179_, 1);
v_fst_5181_ = lean_ctor_get(v_a_5180_, 0);
lean_inc(v_fst_5181_);
lean_dec(v_a_5180_);
v___x_5182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5181_, v_x_5171_);
lean_dec(v_fst_5181_);
return v___x_5182_;
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v_x_5171_);
v_a_5183_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5179_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5179_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_5191_; lean_object* v___x_5192_; 
v_fvarId_5191_ = lean_ctor_get(v_x_5170_, 0);
lean_inc(v_fvarId_5191_);
lean_dec_ref_known(v_x_5170_, 1);
v___x_5192_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5191_, v_a_5172_, v_a_5174_, v_a_5175_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5194_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_a_5193_);
lean_dec_ref_known(v___x_5192_, 1);
v___x_5194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5193_, v_x_5171_);
lean_dec(v_a_5193_);
return v___x_5194_;
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_x_5171_);
v_a_5195_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5192_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5192_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5203_; lean_object* v___x_5204_; 
v_mvarId_5203_ = lean_ctor_get(v_x_5170_, 0);
lean_inc(v_mvarId_5203_);
lean_dec_ref_known(v_x_5170_, 1);
v___x_5204_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5203_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v___x_5206_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref_known(v___x_5204_, 1);
v___x_5206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5205_, v_x_5171_);
lean_dec(v_a_5205_);
return v___x_5206_;
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
lean_dec(v_x_5171_);
v_a_5207_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5214_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5214_ == 0)
{
v___x_5209_ = v___x_5204_;
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5204_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
case 5:
{
lean_object* v_fn_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v_fn_5215_ = lean_ctor_get(v_x_5170_, 0);
lean_inc_ref(v_fn_5215_);
lean_dec_ref_known(v_x_5170_, 2);
v___x_5216_ = lean_unsigned_to_nat(1u);
v___x_5217_ = lean_nat_add(v_x_5171_, v___x_5216_);
lean_dec(v_x_5171_);
v_x_5170_ = v_fn_5215_;
v_x_5171_ = v___x_5217_;
goto _start;
}
case 10:
{
lean_object* v_expr_5219_; 
v_expr_5219_ = lean_ctor_get(v_x_5170_, 1);
lean_inc_ref(v_expr_5219_);
lean_dec_ref_known(v_x_5170_, 2);
v_x_5170_ = v_expr_5219_;
goto _start;
}
case 8:
{
lean_object* v_body_5221_; 
v_body_5221_ = lean_ctor_get(v_x_5170_, 3);
lean_inc_ref(v_body_5221_);
lean_dec_ref_known(v_x_5170_, 4);
v_x_5170_ = v_body_5221_;
goto _start;
}
case 6:
{
lean_object* v_body_5223_; lean_object* v_zero_5224_; uint8_t v_isZero_5225_; 
v_body_5223_ = lean_ctor_get(v_x_5170_, 2);
lean_inc_ref(v_body_5223_);
lean_dec_ref_known(v_x_5170_, 3);
v_zero_5224_ = lean_unsigned_to_nat(0u);
v_isZero_5225_ = lean_nat_dec_eq(v_x_5171_, v_zero_5224_);
if (v_isZero_5225_ == 1)
{
uint8_t v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
lean_dec_ref(v_body_5223_);
lean_dec(v_x_5171_);
v___x_5226_ = 0;
v___x_5227_ = lean_box(v___x_5226_);
v___x_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
return v___x_5228_;
}
else
{
lean_object* v_one_5229_; lean_object* v_n_5230_; 
v_one_5229_ = lean_unsigned_to_nat(1u);
v_n_5230_ = lean_nat_sub(v_x_5171_, v_one_5229_);
lean_dec(v_x_5171_);
v_x_5170_ = v_body_5223_;
v_x_5171_ = v_n_5230_;
goto _start;
}
}
default: 
{
uint8_t v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
lean_dec(v_x_5171_);
lean_dec_ref(v_x_5170_);
v___x_5232_ = 2;
v___x_5233_ = lean_box(v___x_5232_);
v___x_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5233_);
return v___x_5234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_5235_, lean_object* v_x_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_5235_, v_x_5236_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_);
lean_dec(v_a_5240_);
lean_dec_ref(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_a_5237_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_){
_start:
{
switch(lean_obj_tag(v_x_5243_))
{
case 1:
{
lean_object* v_fvarId_5249_; lean_object* v___x_5250_; 
v_fvarId_5249_ = lean_ctor_get(v_x_5243_, 0);
lean_inc(v_fvarId_5249_);
lean_dec_ref_known(v_x_5243_, 1);
v___x_5250_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5249_, v_a_5244_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc(v_a_5251_);
lean_dec_ref_known(v___x_5250_, 1);
v___x_5252_ = lean_unsigned_to_nat(0u);
v___x_5253_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5251_, v___x_5252_);
lean_dec(v_a_5251_);
return v___x_5253_;
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
v_a_5254_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5250_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5250_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5262_; lean_object* v___x_5263_; 
v_mvarId_5262_ = lean_ctor_get(v_x_5243_, 0);
lean_inc(v_mvarId_5262_);
lean_dec_ref_known(v_x_5243_, 1);
v___x_5263_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5262_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5263_) == 0)
{
lean_object* v_a_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
lean_inc(v_a_5264_);
lean_dec_ref_known(v___x_5263_, 1);
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5264_, v___x_5265_);
lean_dec(v_a_5264_);
return v___x_5266_;
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
v_a_5267_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5263_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5263_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
case 3:
{
uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_dec_ref_known(v_x_5243_, 1);
v___x_5275_ = 1;
v___x_5276_ = lean_box(v___x_5275_);
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
case 4:
{
lean_object* v_declName_5278_; lean_object* v_us_5279_; lean_object* v___x_5280_; 
v_declName_5278_ = lean_ctor_get(v_x_5243_, 0);
lean_inc(v_declName_5278_);
v_us_5279_ = lean_ctor_get(v_x_5243_, 1);
lean_inc(v_us_5279_);
lean_dec_ref_known(v_x_5243_, 2);
v___x_5280_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5278_, v_us_5279_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v_fst_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
lean_inc(v_a_5281_);
lean_dec_ref_known(v___x_5280_, 1);
v_fst_5282_ = lean_ctor_get(v_a_5281_, 0);
lean_inc(v_fst_5282_);
lean_dec(v_a_5281_);
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5282_, v___x_5283_);
lean_dec(v_fst_5282_);
return v___x_5284_;
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5285_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5280_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5280_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
case 5:
{
lean_object* v_fn_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v_fn_5293_ = lean_ctor_get(v_x_5243_, 0);
lean_inc_ref(v_fn_5293_);
lean_dec_ref_known(v_x_5243_, 2);
v___x_5294_ = lean_unsigned_to_nat(1u);
v___x_5295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_5293_, v___x_5294_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
return v___x_5295_;
}
case 6:
{
uint8_t v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
lean_dec_ref_known(v_x_5243_, 3);
v___x_5296_ = 0;
v___x_5297_ = lean_box(v___x_5296_);
v___x_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
return v___x_5298_;
}
case 7:
{
uint8_t v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
lean_dec_ref_known(v_x_5243_, 3);
v___x_5299_ = 1;
v___x_5300_ = lean_box(v___x_5299_);
v___x_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5300_);
return v___x_5301_;
}
case 8:
{
lean_object* v_body_5302_; 
v_body_5302_ = lean_ctor_get(v_x_5243_, 3);
lean_inc_ref(v_body_5302_);
lean_dec_ref_known(v_x_5243_, 4);
v_x_5243_ = v_body_5302_;
goto _start;
}
case 9:
{
uint8_t v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
lean_dec_ref_known(v_x_5243_, 1);
v___x_5304_ = 0;
v___x_5305_ = lean_box(v___x_5304_);
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5305_);
return v___x_5306_;
}
case 10:
{
lean_object* v_expr_5307_; 
v_expr_5307_ = lean_ctor_get(v_x_5243_, 1);
lean_inc_ref(v_expr_5307_);
lean_dec_ref_known(v_x_5243_, 2);
v_x_5243_ = v_expr_5307_;
goto _start;
}
default: 
{
uint8_t v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
lean_dec_ref(v_x_5243_);
v___x_5309_ = 2;
v___x_5310_ = lean_box(v___x_5309_);
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_){
_start:
{
lean_object* v_res_5318_; 
v_res_5318_ = l_Lean_Meta_isTypeQuick(v_x_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_);
lean_dec(v_a_5316_);
lean_dec_ref(v_a_5315_);
lean_dec(v_a_5314_);
lean_dec_ref(v_a_5313_);
return v_res_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_){
_start:
{
lean_object* v___x_5325_; 
lean_inc_ref(v_e_5319_);
v___x_5325_ = l_Lean_Meta_isTypeQuick(v_e_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5375_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5328_ = v___x_5325_;
v_isShared_5329_ = v_isSharedCheck_5375_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5325_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5375_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
uint8_t v___x_5330_; 
v___x_5330_ = lean_unbox(v_a_5326_);
lean_dec(v_a_5326_);
switch(v___x_5330_)
{
case 0:
{
uint8_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5334_; 
lean_dec_ref(v_e_5319_);
v___x_5331_ = 0;
v___x_5332_ = lean_box(v___x_5331_);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 0, v___x_5332_);
v___x_5334_ = v___x_5328_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
case 1:
{
uint8_t v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5339_; 
lean_dec_ref(v_e_5319_);
v___x_5336_ = 1;
v___x_5337_ = lean_box(v___x_5336_);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 0, v___x_5337_);
v___x_5339_ = v___x_5328_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5337_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
default: 
{
lean_object* v___x_5341_; 
lean_del_object(v___x_5328_);
lean_inc(v_a_5323_);
lean_inc_ref(v_a_5322_);
lean_inc(v_a_5321_);
lean_inc_ref(v_a_5320_);
v___x_5341_ = lean_infer_type(v_e_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5343_; 
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
lean_inc(v_a_5342_);
lean_dec_ref_known(v___x_5341_, 1);
v___x_5343_ = l_Lean_Meta_whnfD(v_a_5342_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5358_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5346_ = v___x_5343_;
v_isShared_5347_ = v_isSharedCheck_5358_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5343_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5358_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
if (lean_obj_tag(v_a_5344_) == 3)
{
uint8_t v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5351_; 
lean_dec_ref_known(v_a_5344_, 1);
v___x_5348_ = 1;
v___x_5349_ = lean_box(v___x_5348_);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 0, v___x_5349_);
v___x_5351_ = v___x_5346_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
else
{
uint8_t v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5356_; 
lean_dec(v_a_5344_);
v___x_5353_ = 0;
v___x_5354_ = lean_box(v___x_5353_);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 0, v___x_5354_);
v___x_5356_ = v___x_5346_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
else
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5366_; 
v_a_5359_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5361_ = v___x_5343_;
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5343_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5364_; 
if (v_isShared_5362_ == 0)
{
v___x_5364_ = v___x_5361_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5359_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
v_a_5367_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5341_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5341_);
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
}
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec_ref(v_e_5319_);
v_a_5376_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5325_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5325_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_Meta_isType(v_e_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_5391_){
_start:
{
switch(lean_obj_tag(v_x_5391_))
{
case 7:
{
lean_object* v_body_5392_; 
v_body_5392_ = lean_ctor_get(v_x_5391_, 2);
v_x_5391_ = v_body_5392_;
goto _start;
}
case 3:
{
lean_object* v_u_5394_; lean_object* v___x_5395_; 
v_u_5394_ = lean_ctor_get(v_x_5391_, 0);
lean_inc(v_u_5394_);
v___x_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5395_, 0, v_u_5394_);
return v___x_5395_;
}
default: 
{
lean_object* v___x_5396_; 
v___x_5396_ = lean_box(0);
return v___x_5396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_5397_);
lean_dec_ref(v_x_5397_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5399_, lean_object* v_body_5400_, lean_object* v_x_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5399_, v_body_5400_, v_x_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5410_, lean_object* v_xs_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_){
_start:
{
lean_object* v_l_5418_; 
switch(lean_obj_tag(v_type_5410_))
{
case 3:
{
lean_object* v_u_5421_; 
lean_dec_ref(v_xs_5411_);
v_u_5421_ = lean_ctor_get(v_type_5410_, 0);
lean_inc(v_u_5421_);
lean_dec_ref_known(v_type_5410_, 1);
v_l_5418_ = v_u_5421_;
goto v___jp_5417_;
}
case 7:
{
lean_object* v_binderName_5422_; lean_object* v_binderType_5423_; lean_object* v_body_5424_; uint8_t v_binderInfo_5425_; lean_object* v___f_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v_binderName_5422_ = lean_ctor_get(v_type_5410_, 0);
lean_inc(v_binderName_5422_);
v_binderType_5423_ = lean_ctor_get(v_type_5410_, 1);
lean_inc_ref(v_binderType_5423_);
v_body_5424_ = lean_ctor_get(v_type_5410_, 2);
lean_inc_ref(v_body_5424_);
v_binderInfo_5425_ = lean_ctor_get_uint8(v_type_5410_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5410_, 3);
lean_inc_ref(v_xs_5411_);
v___f_5426_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5426_, 0, v_xs_5411_);
lean_closure_set(v___f_5426_, 1, v_body_5424_);
v___x_5427_ = lean_expr_instantiate_rev(v_binderType_5423_, v_xs_5411_);
lean_dec_ref(v_xs_5411_);
lean_dec_ref(v_binderType_5423_);
v___x_5428_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5422_, v_binderInfo_5425_, v___x_5427_, v___f_5426_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_);
return v___x_5428_;
}
default: 
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = lean_expr_instantiate_rev(v_type_5410_, v_xs_5411_);
lean_dec_ref(v_xs_5411_);
lean_dec_ref(v_type_5410_);
v___x_5430_ = l_Lean_Meta_whnfD(v___x_5429_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5442_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5433_ = v___x_5430_;
v_isShared_5434_ = v_isSharedCheck_5442_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5430_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5442_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
switch(lean_obj_tag(v_a_5431_))
{
case 3:
{
lean_object* v_u_5435_; 
lean_del_object(v___x_5433_);
v_u_5435_ = lean_ctor_get(v_a_5431_, 0);
lean_inc(v_u_5435_);
lean_dec_ref_known(v_a_5431_, 1);
v_l_5418_ = v_u_5435_;
goto v___jp_5417_;
}
case 7:
{
lean_object* v___x_5436_; 
lean_del_object(v___x_5433_);
v___x_5436_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5410_ = v_a_5431_;
v_xs_5411_ = v___x_5436_;
goto _start;
}
default: 
{
lean_object* v___x_5438_; lean_object* v___x_5440_; 
lean_dec(v_a_5431_);
v___x_5438_ = lean_box(0);
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 0, v___x_5438_);
v___x_5440_ = v___x_5433_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
else
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
v_a_5443_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5445_ = v___x_5430_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5430_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_a_5443_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
}
}
v___jp_5417_:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5419_, 0, v_l_5418_);
v___x_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
return v___x_5420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5451_, lean_object* v_body_5452_, lean_object* v_x_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5459_ = lean_array_push(v_xs_5451_, v_x_5453_);
v___x_5460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5452_, v___x_5459_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5461_, lean_object* v_xs_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5461_, v_xs_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_);
lean_dec(v_a_5466_);
lean_dec_ref(v_a_5465_);
lean_dec(v_a_5464_);
lean_dec_ref(v_a_5463_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5469_, lean_object* v_cache_5470_, lean_object* v_a_x3f_5471_){
_start:
{
lean_object* v___x_5473_; lean_object* v_mctx_5474_; lean_object* v_zetaDeltaFVarIds_5475_; lean_object* v_postponed_5476_; lean_object* v_diag_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5487_; 
v___x_5473_ = lean_st_ref_take(v_a_5469_);
v_mctx_5474_ = lean_ctor_get(v___x_5473_, 0);
v_zetaDeltaFVarIds_5475_ = lean_ctor_get(v___x_5473_, 2);
v_postponed_5476_ = lean_ctor_get(v___x_5473_, 3);
v_diag_5477_ = lean_ctor_get(v___x_5473_, 4);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; 
v_unused_5488_ = lean_ctor_get(v___x_5473_, 1);
lean_dec(v_unused_5488_);
v___x_5479_ = v___x_5473_;
v_isShared_5480_ = v_isSharedCheck_5487_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_diag_5477_);
lean_inc(v_postponed_5476_);
lean_inc(v_zetaDeltaFVarIds_5475_);
lean_inc(v_mctx_5474_);
lean_dec(v___x_5473_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5487_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5481_; lean_object* v___x_5483_; 
v___x_5481_ = lean_box(0);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 1, v_cache_5470_);
v___x_5483_ = v___x_5479_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_mctx_5474_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v_cache_5470_);
lean_ctor_set(v_reuseFailAlloc_5486_, 2, v_zetaDeltaFVarIds_5475_);
lean_ctor_set(v_reuseFailAlloc_5486_, 3, v_postponed_5476_);
lean_ctor_set(v_reuseFailAlloc_5486_, 4, v_diag_5477_);
v___x_5483_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = lean_st_ref_put(v_a_5469_, v___x_5483_);
v___x_5485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5481_);
return v___x_5485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5489_, lean_object* v_cache_5490_, lean_object* v_a_x3f_5491_, lean_object* v___y_5492_){
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5489_, v_cache_5490_, v_a_x3f_5491_);
lean_dec(v_a_x3f_5491_);
lean_dec(v_a_5489_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_){
_start:
{
lean_object* v___x_5500_; 
v___x_5500_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5494_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v_cache_5503_; lean_object* v___x_5504_; 
v___x_5501_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5502_ = lean_st_ref_get(v_a_5496_);
v_cache_5503_ = lean_ctor_get(v___x_5502_, 1);
lean_inc_ref(v_cache_5503_);
lean_dec(v___x_5502_);
v___x_5504_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5494_, v___x_5501_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5521_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5507_ = v___x_5504_;
v_isShared_5508_ = v_isSharedCheck_5521_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5504_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5521_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
lean_inc(v_a_5505_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set_tag(v___x_5507_, 1);
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
v___x_5511_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5496_, v_cache_5503_, v___x_5510_);
lean_dec_ref(v___x_5510_);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5511_);
if (v_isSharedCheck_5518_ == 0)
{
lean_object* v_unused_5519_; 
v_unused_5519_ = lean_ctor_get(v___x_5511_, 0);
lean_dec(v_unused_5519_);
v___x_5513_ = v___x_5511_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_dec(v___x_5511_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 0, v_a_5505_);
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5505_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
v_a_5522_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5522_);
lean_dec_ref_known(v___x_5504_, 1);
v___x_5523_ = lean_box(0);
v___x_5524_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5496_, v_cache_5503_, v___x_5523_);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; 
v_unused_5532_ = lean_ctor_get(v___x_5524_, 0);
lean_dec(v_unused_5532_);
v___x_5526_ = v___x_5524_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_dec(v___x_5524_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
lean_ctor_set_tag(v___x_5526_, 1);
lean_ctor_set(v___x_5526_, 0, v_a_5522_);
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5522_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
else
{
lean_object* v___x_5533_; 
lean_dec_ref(v_type_5494_);
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5500_);
return v___x_5533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_);
lean_dec(v_a_5538_);
lean_dec_ref(v_a_5537_);
lean_dec(v_a_5536_);
lean_dec_ref(v_a_5535_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_){
_start:
{
lean_object* v___x_5547_; 
v___x_5547_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5562_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5562_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5562_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
if (lean_obj_tag(v_a_5548_) == 0)
{
uint8_t v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5555_; 
v___x_5552_ = 0;
v___x_5553_ = lean_box(v___x_5552_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v___x_5553_);
v___x_5555_ = v___x_5550_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
return v___x_5555_;
}
}
else
{
uint8_t v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5560_; 
lean_dec_ref_known(v_a_5548_, 1);
v___x_5557_ = 1;
v___x_5558_ = lean_box(v___x_5557_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v___x_5558_);
v___x_5560_ = v___x_5550_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
else
{
lean_object* v_a_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5570_; 
v_a_5563_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5565_ = v___x_5547_;
v_isShared_5566_ = v_isSharedCheck_5570_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_a_5563_);
lean_dec(v___x_5547_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5570_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5568_; 
if (v_isShared_5566_ == 0)
{
v___x_5568_ = v___x_5565_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_){
_start:
{
lean_object* v_res_5577_; 
v_res_5577_ = l_Lean_Meta_isTypeFormerType(v_type_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_);
lean_dec(v_a_5575_);
lean_dec_ref(v_a_5574_);
lean_dec(v_a_5573_);
lean_dec_ref(v_a_5572_);
return v_res_5577_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5578_, lean_object* v_x_5579_){
_start:
{
if (lean_obj_tag(v_x_5578_) == 0)
{
if (lean_obj_tag(v_x_5579_) == 0)
{
uint8_t v___x_5580_; 
v___x_5580_ = 1;
return v___x_5580_;
}
else
{
uint8_t v___x_5581_; 
v___x_5581_ = 0;
return v___x_5581_;
}
}
else
{
if (lean_obj_tag(v_x_5579_) == 0)
{
uint8_t v___x_5582_; 
v___x_5582_ = 0;
return v___x_5582_;
}
else
{
lean_object* v_val_5583_; lean_object* v_val_5584_; uint8_t v___x_5585_; 
v_val_5583_ = lean_ctor_get(v_x_5578_, 0);
v_val_5584_ = lean_ctor_get(v_x_5579_, 0);
v___x_5585_ = lean_level_eq(v_val_5583_, v_val_5584_);
return v___x_5585_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5586_, lean_object* v_x_5587_){
_start:
{
uint8_t v_res_5588_; lean_object* v_r_5589_; 
v_res_5588_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5586_, v_x_5587_);
lean_dec(v_x_5587_);
lean_dec(v_x_5586_);
v_r_5589_ = lean_box(v_res_5588_);
return v_r_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_){
_start:
{
lean_object* v___x_5598_; 
v___x_5598_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5609_; 
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5601_ = v___x_5598_;
v_isShared_5602_ = v_isSharedCheck_5609_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5598_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5609_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5603_; uint8_t v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5607_; 
v___x_5603_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5604_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5599_, v___x_5603_);
lean_dec(v_a_5599_);
v___x_5605_ = lean_box(v___x_5604_);
if (v_isShared_5602_ == 0)
{
lean_ctor_set(v___x_5601_, 0, v___x_5605_);
v___x_5607_ = v___x_5601_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v___x_5605_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5617_; 
v_a_5610_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5612_ = v___x_5598_;
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5598_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5615_; 
if (v_isShared_5613_ == 0)
{
v___x_5615_ = v___x_5612_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l_Lean_Meta_isPropFormerType(v_type_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_);
lean_dec(v_a_5622_);
lean_dec_ref(v_a_5621_);
lean_dec(v_a_5620_);
lean_dec_ref(v_a_5619_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_){
_start:
{
lean_object* v___x_5631_; 
lean_inc(v_a_5629_);
lean_inc_ref(v_a_5628_);
lean_inc(v_a_5627_);
lean_inc_ref(v_a_5626_);
v___x_5631_ = lean_infer_type(v_e_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_object* v_a_5632_; lean_object* v___x_5633_; 
v_a_5632_ = lean_ctor_get(v___x_5631_, 0);
lean_inc(v_a_5632_);
lean_dec_ref_known(v___x_5631_, 1);
v___x_5633_ = l_Lean_Meta_isTypeFormerType(v_a_5632_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
return v___x_5633_;
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
v_a_5634_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5636_ = v___x_5631_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5631_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l_Lean_Meta_isTypeFormer(v_e_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5649_, lean_object* v_maxFVars_x3f_5650_, lean_object* v_k_5651_, uint8_t v_cleanupAnnotations_5652_, uint8_t v_whnfType_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
lean_object* v___f_5659_; lean_object* v___x_5660_; 
v___f_5659_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5659_, 0, v_k_5651_);
v___x_5660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5649_, v_maxFVars_x3f_5650_, v___f_5659_, v_cleanupAnnotations_5652_, v_whnfType_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5660_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5660_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
v_a_5669_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5660_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5660_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5677_, lean_object* v_maxFVars_x3f_5678_, lean_object* v_k_5679_, lean_object* v_cleanupAnnotations_5680_, lean_object* v_whnfType_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5687_; uint8_t v_whnfType_boxed_5688_; lean_object* v_res_5689_; 
v_cleanupAnnotations_boxed_5687_ = lean_unbox(v_cleanupAnnotations_5680_);
v_whnfType_boxed_5688_ = lean_unbox(v_whnfType_5681_);
v_res_5689_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5677_, v_maxFVars_x3f_5678_, v_k_5679_, v_cleanupAnnotations_boxed_5687_, v_whnfType_boxed_5688_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5690_, lean_object* v_type_5691_, lean_object* v_maxFVars_x3f_5692_, lean_object* v_k_5693_, uint8_t v_cleanupAnnotations_5694_, uint8_t v_whnfType_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5691_, v_maxFVars_x3f_5692_, v_k_5693_, v_cleanupAnnotations_5694_, v_whnfType_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5702_, lean_object* v_type_5703_, lean_object* v_maxFVars_x3f_5704_, lean_object* v_k_5705_, lean_object* v_cleanupAnnotations_5706_, lean_object* v_whnfType_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5713_; uint8_t v_whnfType_boxed_5714_; lean_object* v_res_5715_; 
v_cleanupAnnotations_boxed_5713_ = lean_unbox(v_cleanupAnnotations_5706_);
v_whnfType_boxed_5714_ = lean_unbox(v_whnfType_5707_);
v_res_5715_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5702_, v_type_5703_, v_maxFVars_x3f_5704_, v_k_5705_, v_cleanupAnnotations_boxed_5713_, v_whnfType_boxed_5714_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
lean_dec(v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
return v_res_5715_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5716_, lean_object* v_as_5717_, size_t v_i_5718_, size_t v_stop_5719_){
_start:
{
uint8_t v___x_5720_; 
v___x_5720_ = lean_usize_dec_eq(v_i_5718_, v_stop_5719_);
if (v___x_5720_ == 0)
{
lean_object* v___x_5721_; uint8_t v___x_5722_; 
v___x_5721_ = lean_array_uget_borrowed(v_as_5717_, v_i_5718_);
v___x_5722_ = lean_expr_eqv(v_a_5716_, v___x_5721_);
if (v___x_5722_ == 0)
{
size_t v___x_5723_; size_t v___x_5724_; 
v___x_5723_ = ((size_t)1ULL);
v___x_5724_ = lean_usize_add(v_i_5718_, v___x_5723_);
v_i_5718_ = v___x_5724_;
goto _start;
}
else
{
return v___x_5722_;
}
}
else
{
uint8_t v___x_5726_; 
v___x_5726_ = 0;
return v___x_5726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5727_, lean_object* v_as_5728_, lean_object* v_i_5729_, lean_object* v_stop_5730_){
_start:
{
size_t v_i_boxed_5731_; size_t v_stop_boxed_5732_; uint8_t v_res_5733_; lean_object* v_r_5734_; 
v_i_boxed_5731_ = lean_unbox_usize(v_i_5729_);
lean_dec(v_i_5729_);
v_stop_boxed_5732_ = lean_unbox_usize(v_stop_5730_);
lean_dec(v_stop_5730_);
v_res_5733_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5727_, v_as_5728_, v_i_boxed_5731_, v_stop_boxed_5732_);
lean_dec_ref(v_as_5728_);
lean_dec_ref(v_a_5727_);
v_r_5734_ = lean_box(v_res_5733_);
return v_r_5734_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5735_, lean_object* v_a_5736_){
_start:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; uint8_t v___x_5739_; 
v___x_5737_ = lean_unsigned_to_nat(0u);
v___x_5738_ = lean_array_get_size(v_as_5735_);
v___x_5739_ = lean_nat_dec_lt(v___x_5737_, v___x_5738_);
if (v___x_5739_ == 0)
{
return v___x_5739_;
}
else
{
size_t v___x_5740_; size_t v___x_5741_; uint8_t v___x_5742_; 
v___x_5740_ = ((size_t)0ULL);
v___x_5741_ = lean_usize_of_nat(v___x_5738_);
v___x_5742_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5736_, v_as_5735_, v___x_5740_, v___x_5741_);
return v___x_5742_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5743_, lean_object* v_a_5744_){
_start:
{
uint8_t v_res_5745_; lean_object* v_r_5746_; 
v_res_5745_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5743_, v_a_5744_);
lean_dec_ref(v_a_5744_);
lean_dec_ref(v_as_5743_);
v_r_5746_ = lean_box(v_res_5745_);
return v_r_5746_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5747_, lean_object* v_e_5748_){
_start:
{
uint8_t v___x_5749_; lean_object* v_d_5751_; lean_object* v_b_5752_; 
v___x_5749_ = l_Lean_Expr_hasFVar(v_e_5748_);
if (v___x_5749_ == 0)
{
lean_dec_ref(v_e_5748_);
return v___x_5749_;
}
else
{
switch(lean_obj_tag(v_e_5748_))
{
case 7:
{
lean_object* v_binderType_5755_; lean_object* v_body_5756_; 
v_binderType_5755_ = lean_ctor_get(v_e_5748_, 1);
lean_inc_ref(v_binderType_5755_);
v_body_5756_ = lean_ctor_get(v_e_5748_, 2);
lean_inc_ref(v_body_5756_);
lean_dec_ref_known(v_e_5748_, 3);
v_d_5751_ = v_binderType_5755_;
v_b_5752_ = v_body_5756_;
goto v___jp_5750_;
}
case 6:
{
lean_object* v_binderType_5757_; lean_object* v_body_5758_; 
v_binderType_5757_ = lean_ctor_get(v_e_5748_, 1);
lean_inc_ref(v_binderType_5757_);
v_body_5758_ = lean_ctor_get(v_e_5748_, 2);
lean_inc_ref(v_body_5758_);
lean_dec_ref_known(v_e_5748_, 3);
v_d_5751_ = v_binderType_5757_;
v_b_5752_ = v_body_5758_;
goto v___jp_5750_;
}
case 10:
{
lean_object* v_expr_5759_; 
v_expr_5759_ = lean_ctor_get(v_e_5748_, 1);
lean_inc_ref(v_expr_5759_);
lean_dec_ref_known(v_e_5748_, 2);
v_e_5748_ = v_expr_5759_;
goto _start;
}
case 8:
{
lean_object* v_type_5761_; lean_object* v_value_5762_; lean_object* v_body_5763_; uint8_t v___x_5764_; 
v_type_5761_ = lean_ctor_get(v_e_5748_, 1);
lean_inc_ref(v_type_5761_);
v_value_5762_ = lean_ctor_get(v_e_5748_, 2);
lean_inc_ref(v_value_5762_);
v_body_5763_ = lean_ctor_get(v_e_5748_, 3);
lean_inc_ref(v_body_5763_);
lean_dec_ref_known(v_e_5748_, 4);
v___x_5764_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5747_, v_type_5761_);
if (v___x_5764_ == 0)
{
uint8_t v___x_5765_; 
v___x_5765_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5747_, v_value_5762_);
if (v___x_5765_ == 0)
{
v_e_5748_ = v_body_5763_;
goto _start;
}
else
{
lean_dec_ref(v_body_5763_);
return v___x_5749_;
}
}
else
{
lean_dec_ref(v_body_5763_);
lean_dec_ref(v_value_5762_);
return v___x_5749_;
}
}
case 5:
{
lean_object* v_fn_5767_; lean_object* v_arg_5768_; uint8_t v___x_5769_; 
v_fn_5767_ = lean_ctor_get(v_e_5748_, 0);
lean_inc_ref(v_fn_5767_);
v_arg_5768_ = lean_ctor_get(v_e_5748_, 1);
lean_inc_ref(v_arg_5768_);
lean_dec_ref_known(v_e_5748_, 2);
v___x_5769_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5747_, v_fn_5767_);
if (v___x_5769_ == 0)
{
v_e_5748_ = v_arg_5768_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5768_);
return v___x_5749_;
}
}
case 11:
{
lean_object* v_struct_5771_; 
v_struct_5771_ = lean_ctor_get(v_e_5748_, 2);
lean_inc_ref(v_struct_5771_);
lean_dec_ref_known(v_e_5748_, 3);
v_e_5748_ = v_struct_5771_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5773_; lean_object* v___x_5774_; uint8_t v___x_5775_; 
v_fvarId_5773_ = lean_ctor_get(v_e_5748_, 0);
lean_inc(v_fvarId_5773_);
lean_dec_ref_known(v_e_5748_, 1);
v___x_5774_ = l_Lean_Expr_fvar___override(v_fvarId_5773_);
v___x_5775_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5747_, v___x_5774_);
lean_dec_ref(v___x_5774_);
return v___x_5775_;
}
default: 
{
uint8_t v___x_5776_; 
lean_dec_ref(v_e_5748_);
v___x_5776_ = 0;
return v___x_5776_;
}
}
}
v___jp_5750_:
{
uint8_t v___x_5753_; 
v___x_5753_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5747_, v_d_5751_);
if (v___x_5753_ == 0)
{
v_e_5748_ = v_b_5752_;
goto _start;
}
else
{
lean_dec_ref(v_b_5752_);
return v___x_5749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5777_, lean_object* v_e_5778_){
_start:
{
uint8_t v_res_5779_; lean_object* v_r_5780_; 
v_res_5779_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5777_, v_e_5778_);
lean_dec_ref(v_xs_5777_);
v_r_5780_ = lean_box(v_res_5779_);
return v_r_5780_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5783_ = l_Lean_stringToMessageData(v___x_5782_);
return v___x_5783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; 
v___x_5785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5786_ = l_Lean_stringToMessageData(v___x_5785_);
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5787_, lean_object* v_type_5788_, lean_object* v_as_5789_, size_t v_sz_5790_, size_t v_i_5791_, lean_object* v_b_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v_a_5799_; uint8_t v___x_5803_; 
v___x_5803_ = lean_usize_dec_lt(v_i_5791_, v_sz_5790_);
if (v___x_5803_ == 0)
{
lean_object* v___x_5804_; 
lean_dec_ref(v_type_5788_);
v___x_5804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5804_, 0, v_b_5792_);
return v___x_5804_;
}
else
{
lean_object* v___x_5805_; lean_object* v_a_5806_; uint8_t v___x_5807_; 
v___x_5805_ = lean_box(0);
v_a_5806_ = lean_array_uget_borrowed(v_as_5789_, v_i_5791_);
lean_inc(v_a_5806_);
v___x_5807_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5787_, v_a_5806_);
if (v___x_5807_ == 0)
{
v_a_5799_ = v___x_5805_;
goto v___jp_5798_;
}
else
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; 
v___x_5808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5806_);
v___x_5809_ = l_Lean_MessageData_ofExpr(v_a_5806_);
v___x_5810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5810_, 0, v___x_5808_);
lean_ctor_set(v___x_5810_, 1, v___x_5809_);
v___x_5811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5810_);
lean_ctor_set(v___x_5812_, 1, v___x_5811_);
lean_inc_ref(v_type_5788_);
v___x_5813_ = l_Lean_MessageData_ofExpr(v_type_5788_);
v___x_5814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5814_, 0, v___x_5812_);
lean_ctor_set(v___x_5814_, 1, v___x_5813_);
v___x_5815_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5814_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_dec_ref_known(v___x_5815_, 1);
v_a_5799_ = v___x_5805_;
goto v___jp_5798_;
}
else
{
lean_dec_ref(v_type_5788_);
return v___x_5815_;
}
}
}
v___jp_5798_:
{
size_t v___x_5800_; size_t v___x_5801_; 
v___x_5800_ = ((size_t)1ULL);
v___x_5801_ = lean_usize_add(v_i_5791_, v___x_5800_);
v_i_5791_ = v___x_5801_;
v_b_5792_ = v_a_5799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5816_, lean_object* v_type_5817_, lean_object* v_as_5818_, lean_object* v_sz_5819_, lean_object* v_i_5820_, lean_object* v_b_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
size_t v_sz_boxed_5827_; size_t v_i_boxed_5828_; lean_object* v_res_5829_; 
v_sz_boxed_5827_ = lean_unbox_usize(v_sz_5819_);
lean_dec(v_sz_5819_);
v_i_boxed_5828_ = lean_unbox_usize(v_i_5820_);
lean_dec(v_i_5820_);
v_res_5829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5816_, v_type_5817_, v_as_5818_, v_sz_boxed_5827_, v_i_boxed_5828_, v_b_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v_as_5818_);
lean_dec_ref(v_xs_5816_);
return v_res_5829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5830_, size_t v_i_5831_, lean_object* v_bs_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_){
_start:
{
uint8_t v___x_5838_; 
v___x_5838_ = lean_usize_dec_lt(v_i_5831_, v_sz_5830_);
if (v___x_5838_ == 0)
{
lean_object* v___x_5839_; 
v___x_5839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5839_, 0, v_bs_5832_);
return v___x_5839_;
}
else
{
lean_object* v_v_5840_; lean_object* v___x_5841_; lean_object* v_bs_x27_5842_; lean_object* v___x_5843_; 
v_v_5840_ = lean_array_uget(v_bs_5832_, v_i_5831_);
v___x_5841_ = lean_unsigned_to_nat(0u);
v_bs_x27_5842_ = lean_array_uset(v_bs_5832_, v_i_5831_, v___x_5841_);
lean_inc(v___y_5836_);
lean_inc_ref(v___y_5835_);
lean_inc(v___y_5834_);
lean_inc_ref(v___y_5833_);
v___x_5843_ = lean_infer_type(v_v_5840_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; size_t v___x_5845_; size_t v___x_5846_; lean_object* v___x_5847_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5844_);
lean_dec_ref_known(v___x_5843_, 1);
v___x_5845_ = ((size_t)1ULL);
v___x_5846_ = lean_usize_add(v_i_5831_, v___x_5845_);
v___x_5847_ = lean_array_uset(v_bs_x27_5842_, v_i_5831_, v_a_5844_);
v_i_5831_ = v___x_5846_;
v_bs_5832_ = v___x_5847_;
goto _start;
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_dec_ref(v_bs_x27_5842_);
v_a_5849_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5843_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5843_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5857_, lean_object* v_i_5858_, lean_object* v_bs_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_){
_start:
{
size_t v_sz_boxed_5865_; size_t v_i_boxed_5866_; lean_object* v_res_5867_; 
v_sz_boxed_5865_ = lean_unbox_usize(v_sz_5857_);
lean_dec(v_sz_5857_);
v_i_boxed_5866_ = lean_unbox_usize(v_i_5858_);
lean_dec(v_i_5858_);
v_res_5867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5865_, v_i_boxed_5866_, v_bs_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
return v_res_5867_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5869_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5870_ = l_Lean_stringToMessageData(v___x_5869_);
return v___x_5870_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; 
v___x_5872_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5873_ = l_Lean_stringToMessageData(v___x_5872_);
return v___x_5873_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5875_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5876_ = l_Lean_stringToMessageData(v___x_5875_);
return v___x_5876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5877_, lean_object* v_n_5878_, lean_object* v_xs_5879_, lean_object* v_x_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
lean_object* v___x_5910_; uint8_t v___x_5911_; 
v___x_5910_ = lean_array_get_size(v_xs_5879_);
v___x_5911_ = lean_nat_dec_eq(v___x_5910_, v_n_5878_);
if (v___x_5911_ == 0)
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec_ref(v_xs_5879_);
v___x_5912_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5913_ = l_Lean_MessageData_ofExpr(v_type_5877_);
v___x_5914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5912_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5914_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = l_Nat_reprFast(v_n_5878_);
v___x_5918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
v___x_5919_ = l_Lean_MessageData_ofFormat(v___x_5918_);
v___x_5920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5916_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5920_);
lean_ctor_set(v___x_5922_, 1, v___x_5921_);
v___x_5923_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5922_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
v_a_5924_ = lean_ctor_get(v___x_5923_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5923_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5923_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5923_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
else
{
lean_dec(v_n_5878_);
goto v___jp_5886_;
}
v___jp_5886_:
{
size_t v_sz_5887_; size_t v___x_5888_; lean_object* v___x_5889_; 
v_sz_5887_ = lean_array_size(v_xs_5879_);
v___x_5888_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5879_);
v___x_5889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5887_, v___x_5888_, v_xs_5879_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
if (lean_obj_tag(v___x_5889_) == 0)
{
lean_object* v_a_5890_; lean_object* v___x_5891_; size_t v_sz_5892_; lean_object* v___x_5893_; 
v_a_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5890_);
lean_dec_ref_known(v___x_5889_, 1);
v___x_5891_ = lean_box(0);
v_sz_5892_ = lean_array_size(v_a_5890_);
v___x_5893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5879_, v_type_5877_, v_a_5890_, v_sz_5892_, v___x_5888_, v___x_5891_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
lean_dec_ref(v_xs_5879_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5900_; 
v_isSharedCheck_5900_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5900_ == 0)
{
lean_object* v_unused_5901_; 
v_unused_5901_ = lean_ctor_get(v___x_5893_, 0);
lean_dec(v_unused_5901_);
v___x_5895_ = v___x_5893_;
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
else
{
lean_dec(v___x_5893_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5898_; 
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 0, v_a_5890_);
v___x_5898_ = v___x_5895_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_a_5890_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
else
{
lean_object* v_a_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5909_; 
lean_dec(v_a_5890_);
v_a_5902_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5909_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5909_ == 0)
{
v___x_5904_ = v___x_5893_;
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_a_5902_);
lean_dec(v___x_5893_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5907_; 
if (v_isShared_5905_ == 0)
{
v___x_5907_ = v___x_5904_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_a_5902_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5879_);
lean_dec_ref(v_type_5877_);
return v___x_5889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5932_, lean_object* v_n_5933_, lean_object* v_xs_5934_, lean_object* v_x_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v_res_5941_; 
v_res_5941_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5932_, v_n_5933_, v_xs_5934_, v_x_5935_, v___y_5936_, v___y_5937_, v___y_5938_, v___y_5939_);
lean_dec(v___y_5939_);
lean_dec_ref(v___y_5938_);
lean_dec(v___y_5937_);
lean_dec_ref(v___y_5936_);
lean_dec_ref(v_x_5935_);
return v_res_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5942_, lean_object* v_type_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_){
_start:
{
lean_object* v___f_5949_; lean_object* v___x_5950_; uint8_t v___x_5951_; lean_object* v___x_5952_; 
lean_inc(v_n_5942_);
lean_inc_ref(v_type_5943_);
v___f_5949_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5949_, 0, v_type_5943_);
lean_closure_set(v___f_5949_, 1, v_n_5942_);
v___x_5950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5950_, 0, v_n_5942_);
v___x_5951_ = 0;
v___x_5952_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5943_, v___x_5950_, v___f_5949_, v___x_5951_, v___x_5951_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_);
return v___x_5952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5953_, lean_object* v_type_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_Lean_Meta_arrowDomainsN(v_n_5953_, v_type_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
lean_dec(v_a_5958_);
lean_dec_ref(v_a_5957_);
lean_dec(v_a_5956_);
lean_dec_ref(v_a_5955_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5961_, lean_object* v_e_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_){
_start:
{
lean_object* v___x_5968_; 
lean_inc(v_a_5966_);
lean_inc_ref(v_a_5965_);
lean_inc(v_a_5964_);
lean_inc_ref(v_a_5963_);
v___x_5968_ = lean_infer_type(v_e_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v___x_5970_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v___x_5970_ = l_Lean_Meta_arrowDomainsN(v_n_5961_, v_a_5969_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_);
return v___x_5970_;
}
else
{
lean_object* v_a_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5978_; 
lean_dec(v_n_5961_);
v_a_5971_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5978_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5978_ == 0)
{
v___x_5973_ = v___x_5968_;
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_a_5971_);
lean_dec(v___x_5968_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5974_ == 0)
{
v___x_5976_ = v___x_5973_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5971_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
return v___x_5976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5979_, lean_object* v_e_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_){
_start:
{
lean_object* v_res_5986_; 
v_res_5986_ = l_Lean_Meta_inferArgumentTypesN(v_n_5979_, v_e_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_);
lean_dec(v_a_5984_);
lean_dec_ref(v_a_5983_);
lean_dec(v_a_5982_);
lean_dec_ref(v_a_5981_);
return v_res_5986_;
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
