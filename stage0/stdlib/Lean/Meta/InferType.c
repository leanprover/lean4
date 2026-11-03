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
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2689_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2689_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2689_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2642_; lean_object* v_cache_2643_; lean_object* v_inferType_2644_; lean_object* v___x_2645_; 
v___x_2642_ = lean_st_ref_get(v_a_2512_);
v_cache_2643_ = lean_ctor_get(v___x_2642_, 1);
lean_inc_ref(v_cache_2643_);
lean_dec(v___x_2642_);
v_inferType_2644_ = lean_ctor_get(v_cache_2643_, 0);
lean_inc_ref(v_inferType_2644_);
lean_dec_ref(v_cache_2643_);
lean_inc(v_a_2560_);
v___x_2645_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_2557_, v___x_2558_, v_inferType_2644_, v_a_2560_);
if (lean_obj_tag(v___x_2645_) == 1)
{
lean_object* v_val_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v_expr_2649_; uint64_t v_configKey_2650_; lean_object* v_expr_2651_; uint64_t v_configKey_2652_; uint8_t v___x_2653_; 
v_val_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v_fst_2647_ = lean_ctor_get(v_val_2646_, 0);
lean_inc(v_fst_2647_);
v_snd_2648_ = lean_ctor_get(v_val_2646_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_val_2646_);
v_expr_2649_ = lean_ctor_get(v_a_2560_, 0);
v_configKey_2650_ = lean_ctor_get_uint64(v_a_2560_, sizeof(void*)*1);
v_expr_2651_ = lean_ctor_get(v_fst_2647_, 0);
lean_inc_ref(v_expr_2651_);
v_configKey_2652_ = lean_ctor_get_uint64(v_fst_2647_, sizeof(void*)*1);
lean_dec(v_fst_2647_);
v___x_2653_ = lean_uint64_dec_eq(v_configKey_2650_, v_configKey_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v_expr_2651_);
lean_dec(v_snd_2648_);
lean_dec_ref(v_inferType_2644_);
lean_del_object(v___x_2562_);
goto v___jp_2606_;
}
else
{
size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = ((size_t)64ULL);
v___x_2655_ = lean_expr_equal_budgeted(v_expr_2649_, v_expr_2651_, v___x_2654_);
lean_dec_ref(v_expr_2651_);
switch(v___x_2655_)
{
case 0:
{
lean_dec(v_snd_2648_);
lean_dec_ref(v_inferType_2644_);
lean_del_object(v___x_2562_);
goto v___jp_2606_;
}
case 1:
{
lean_object* v___x_2657_; 
lean_dec_ref(v_inferType_2644_);
lean_dec(v_a_2560_);
lean_dec_ref(v_inferType_2510_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_snd_2648_);
v___x_2657_ = v___x_2562_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_snd_2648_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
default: 
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_cache_2661_; lean_object* v_mctx_2662_; lean_object* v_zetaDeltaFVarIds_2663_; lean_object* v_postponed_2664_; lean_object* v_diag_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_snd_2648_);
lean_del_object(v___x_2562_);
lean_inc(v_a_2560_);
v___x_2659_ = l_Lean_PersistentHashMap_erase___redArg(v___f_2557_, v___x_2558_, v_inferType_2644_, v_a_2560_);
v___x_2660_ = lean_st_ref_take(v_a_2512_);
v_cache_2661_ = lean_ctor_get(v___x_2660_, 1);
v_mctx_2662_ = lean_ctor_get(v___x_2660_, 0);
v_zetaDeltaFVarIds_2663_ = lean_ctor_get(v___x_2660_, 2);
v_postponed_2664_ = lean_ctor_get(v___x_2660_, 3);
v_diag_2665_ = lean_ctor_get(v___x_2660_, 4);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2667_ = v___x_2660_;
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_diag_2665_);
lean_inc(v_postponed_2664_);
lean_inc(v_zetaDeltaFVarIds_2663_);
lean_inc(v_cache_2661_);
lean_inc(v_mctx_2662_);
lean_dec(v___x_2660_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_funInfo_2669_; lean_object* v_synthInstance_2670_; lean_object* v_whnf_2671_; lean_object* v_defEqTrans_2672_; lean_object* v_defEqPerm_2673_; lean_object* v_isUnitLike_2674_; lean_object* v_unfold_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2686_; 
v_funInfo_2669_ = lean_ctor_get(v_cache_2661_, 1);
v_synthInstance_2670_ = lean_ctor_get(v_cache_2661_, 2);
v_whnf_2671_ = lean_ctor_get(v_cache_2661_, 3);
v_defEqTrans_2672_ = lean_ctor_get(v_cache_2661_, 4);
v_defEqPerm_2673_ = lean_ctor_get(v_cache_2661_, 5);
v_isUnitLike_2674_ = lean_ctor_get(v_cache_2661_, 6);
v_unfold_2675_ = lean_ctor_get(v_cache_2661_, 7);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_cache_2661_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v_cache_2661_, 0);
lean_dec(v_unused_2687_);
v___x_2677_ = v_cache_2661_;
v_isShared_2678_ = v_isSharedCheck_2686_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_unfold_2675_);
lean_inc(v_isUnitLike_2674_);
lean_inc(v_defEqPerm_2673_);
lean_inc(v_defEqTrans_2672_);
lean_inc(v_whnf_2671_);
lean_inc(v_synthInstance_2670_);
lean_inc(v_funInfo_2669_);
lean_dec(v_cache_2661_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2686_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2659_);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_funInfo_2669_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_synthInstance_2670_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_whnf_2671_);
lean_ctor_set(v_reuseFailAlloc_2685_, 4, v_defEqTrans_2672_);
lean_ctor_set(v_reuseFailAlloc_2685_, 5, v_defEqPerm_2673_);
lean_ctor_set(v_reuseFailAlloc_2685_, 6, v_isUnitLike_2674_);
lean_ctor_set(v_reuseFailAlloc_2685_, 7, v_unfold_2675_);
v___x_2680_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2680_);
v___x_2682_ = v___x_2667_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_mctx_2662_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_zetaDeltaFVarIds_2663_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_postponed_2664_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_diag_2665_);
v___x_2682_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_st_ref_put(v_a_2512_, v___x_2682_);
goto v___jp_2606_;
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
lean_dec(v___x_2645_);
lean_dec_ref(v_inferType_2644_);
lean_del_object(v___x_2562_);
goto v___jp_2606_;
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
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2604_; 
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2605_);
v___x_2569_ = v___x_2565_;
v_isShared_2570_ = v_isSharedCheck_2604_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2565_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2604_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v_cache_2572_; lean_object* v_mctx_2573_; lean_object* v_zetaDeltaFVarIds_2574_; lean_object* v_postponed_2575_; lean_object* v_diag_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2603_; 
v___x_2571_ = lean_st_ref_take(v_a_2512_);
v_cache_2572_ = lean_ctor_get(v___x_2571_, 1);
v_mctx_2573_ = lean_ctor_get(v___x_2571_, 0);
v_zetaDeltaFVarIds_2574_ = lean_ctor_get(v___x_2571_, 2);
v_postponed_2575_ = lean_ctor_get(v___x_2571_, 3);
v_diag_2576_ = lean_ctor_get(v___x_2571_, 4);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2578_ = v___x_2571_;
v_isShared_2579_ = v_isSharedCheck_2603_;
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
v_isShared_2579_ = v_isSharedCheck_2603_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_inferType_2580_; lean_object* v_funInfo_2581_; lean_object* v_synthInstance_2582_; lean_object* v_whnf_2583_; lean_object* v_defEqTrans_2584_; lean_object* v_defEqPerm_2585_; lean_object* v_isUnitLike_2586_; lean_object* v_unfold_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2602_; 
v_inferType_2580_ = lean_ctor_get(v_cache_2572_, 0);
v_funInfo_2581_ = lean_ctor_get(v_cache_2572_, 1);
v_synthInstance_2582_ = lean_ctor_get(v_cache_2572_, 2);
v_whnf_2583_ = lean_ctor_get(v_cache_2572_, 3);
v_defEqTrans_2584_ = lean_ctor_get(v_cache_2572_, 4);
v_defEqPerm_2585_ = lean_ctor_get(v_cache_2572_, 5);
v_isUnitLike_2586_ = lean_ctor_get(v_cache_2572_, 6);
v_unfold_2587_ = lean_ctor_get(v_cache_2572_, 7);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_cache_2572_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2589_ = v_cache_2572_;
v_isShared_2590_ = v_isSharedCheck_2602_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_unfold_2587_);
lean_inc(v_isUnitLike_2586_);
lean_inc(v_defEqPerm_2585_);
lean_inc(v_defEqTrans_2584_);
lean_inc(v_whnf_2583_);
lean_inc(v_synthInstance_2582_);
lean_inc(v_funInfo_2581_);
lean_inc(v_inferType_2580_);
lean_dec(v_cache_2572_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2602_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_inc(v_a_2566_);
v___x_2591_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2557_, v___x_2558_, v_inferType_2580_, v_a_2560_, v_a_2566_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_funInfo_2581_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_synthInstance_2582_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_whnf_2583_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_defEqTrans_2584_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_defEqPerm_2585_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_isUnitLike_2586_);
lean_ctor_set(v_reuseFailAlloc_2601_, 7, v_unfold_2587_);
v___x_2593_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2595_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___x_2593_);
v___x_2595_ = v___x_2578_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_mctx_2573_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_zetaDeltaFVarIds_2574_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_postponed_2575_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_diag_2576_);
v___x_2595_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_st_ref_put(v_a_2512_, v___x_2595_);
if (v_isShared_2570_ == 0)
{
v___x_2598_ = v___x_2569_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2566_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
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
v___jp_2606_:
{
lean_object* v___x_2607_; lean_object* v_toApplicative_2608_; lean_object* v_toFunctor_2609_; lean_object* v_toSeq_2610_; lean_object* v_toSeqLeft_2611_; lean_object* v_toSeqRight_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_toCold_2628_; lean_object* v_cancelTk_x3f_2629_; 
v___x_2607_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2608_ = lean_ctor_get(v___x_2607_, 0);
v_toFunctor_2609_ = lean_ctor_get(v_toApplicative_2608_, 0);
v_toSeq_2610_ = lean_ctor_get(v_toApplicative_2608_, 2);
v_toSeqLeft_2611_ = lean_ctor_get(v_toApplicative_2608_, 3);
v_toSeqRight_2612_ = lean_ctor_get(v_toApplicative_2608_, 4);
v___f_2613_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2614_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2609_, 2);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toFunctor_2609_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toFunctor_2609_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___f_2615_);
lean_ctor_set(v___x_2617_, 1, v___f_2616_);
lean_inc(v_toSeqRight_2612_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeqRight_2612_);
lean_inc(v_toSeqLeft_2611_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeqLeft_2611_);
lean_inc(v_toSeq_2610_);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toSeq_2610_);
v___x_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2617_);
lean_ctor_set(v___x_2621_, 1, v___f_2613_);
lean_ctor_set(v___x_2621_, 2, v___f_2620_);
lean_ctor_set(v___x_2621_, 3, v___f_2619_);
lean_ctor_set(v___x_2621_, 4, v___f_2618_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___f_2614_);
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2624_ = l_Lean_Core_instMonadRefCoreM;
v___x_2625_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2626_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2625_, v___x_2622_);
v___x_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2623_);
lean_ctor_set(v___x_2627_, 1, v___x_2624_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
v_toCold_2628_ = lean_ctor_get(v_a_2513_, 0);
v_cancelTk_x3f_2629_ = lean_ctor_get(v_toCold_2628_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2629_) == 1)
{
lean_object* v_val_2630_; uint8_t v___x_2631_; 
v_val_2630_ = lean_ctor_get(v_cancelTk_x3f_2629_, 0);
v___x_2631_ = l_IO_CancelToken_isSet(v_val_2630_);
if (v___x_2631_ == 0)
{
lean_dec_ref_known(v___x_2627_, 3);
goto v___jp_2564_;
}
else
{
lean_object* v___x_4256__overap_2632_; lean_object* v___x_2633_; 
v___x_4256__overap_2632_ = l_Lean_throwInterruptException___redArg(v___x_2627_);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
v___x_2633_ = lean_apply_3(v___x_4256__overap_2632_, v_a_2513_, v_a_2514_, lean_box(0));
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_dec_ref_known(v___x_2633_, 1);
goto v___jp_2564_;
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_a_2560_);
lean_dec_ref(v_inferType_2510_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2627_, 3);
goto v___jp_2564_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v_inferType_2510_);
v_a_2690_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2559_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2559_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
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
lean_object* v___x_4231__overap_2543_; lean_object* v___x_2544_; 
v___x_4231__overap_2543_ = l_Lean_throwInterruptException___redArg(v___x_2537_);
lean_inc(v_a_2514_);
lean_inc_ref(v_a_2513_);
v___x_2544_ = lean_apply_3(v___x_4231__overap_2543_, v_a_2513_, v_a_2514_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2698_, lean_object* v_inferType_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2698_, v_inferType_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2758_; uint8_t v_beta_2759_; 
v___x_2758_ = l_Lean_Meta_Context_config(v___y_2707_);
v_beta_2759_ = lean_ctor_get_uint8(v___x_2758_, 13);
if (v_beta_2759_ == 0)
{
lean_dec_ref(v___x_2758_);
goto v___jp_2712_;
}
else
{
uint8_t v_iota_2760_; 
v_iota_2760_ = lean_ctor_get_uint8(v___x_2758_, 12);
if (v_iota_2760_ == 0)
{
lean_dec_ref(v___x_2758_);
goto v___jp_2712_;
}
else
{
uint8_t v_zeta_2761_; 
v_zeta_2761_ = lean_ctor_get_uint8(v___x_2758_, 15);
if (v_zeta_2761_ == 0)
{
lean_dec_ref(v___x_2758_);
goto v___jp_2712_;
}
else
{
uint8_t v_zetaHave_2762_; 
v_zetaHave_2762_ = lean_ctor_get_uint8(v___x_2758_, 18);
if (v_zetaHave_2762_ == 0)
{
lean_dec_ref(v___x_2758_);
goto v___jp_2712_;
}
else
{
uint8_t v_zetaDelta_2763_; 
v_zetaDelta_2763_ = lean_ctor_get_uint8(v___x_2758_, 16);
if (v_zetaDelta_2763_ == 0)
{
lean_dec_ref(v___x_2758_);
goto v___jp_2712_;
}
else
{
uint8_t v_etaStruct_2764_; uint8_t v_proj_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v_etaStruct_2764_ = lean_ctor_get_uint8(v___x_2758_, 10);
v_proj_2765_ = lean_ctor_get_uint8(v___x_2758_, 14);
lean_dec_ref(v___x_2758_);
v___x_2766_ = lean_box(v_proj_2765_);
v___x_2767_ = lean_obj_tag_nat(v___x_2766_);
lean_dec(v___x_2766_);
v___x_2768_ = lean_unsigned_to_nat(2u);
v___x_2769_ = lean_nat_dec_eq(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
goto v___jp_2712_;
}
else
{
uint8_t v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = 0;
v___x_2771_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2764_, v___x_2770_);
if (v___x_2771_ == 0)
{
goto v___jp_2712_;
}
else
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_apply_5(v_x_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, lean_box(0));
return v___x_2772_;
}
}
}
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2713_; uint8_t v_foApprox_2714_; uint8_t v_ctxApprox_2715_; uint8_t v_quasiPatternApprox_2716_; uint8_t v_constApprox_2717_; uint8_t v_isDefEqStuckEx_2718_; uint8_t v_unificationHints_2719_; uint8_t v_proofIrrelevance_2720_; uint8_t v_assignSyntheticOpaque_2721_; uint8_t v_offsetCnstrs_2722_; uint8_t v_transparency_2723_; uint8_t v_univApprox_2724_; uint8_t v_zetaUnused_2725_; uint8_t v_canUnfoldPredicateConfig_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2757_; 
v___x_2713_ = l_Lean_Meta_Context_config(v___y_2707_);
v_foApprox_2714_ = lean_ctor_get_uint8(v___x_2713_, 0);
v_ctxApprox_2715_ = lean_ctor_get_uint8(v___x_2713_, 1);
v_quasiPatternApprox_2716_ = lean_ctor_get_uint8(v___x_2713_, 2);
v_constApprox_2717_ = lean_ctor_get_uint8(v___x_2713_, 3);
v_isDefEqStuckEx_2718_ = lean_ctor_get_uint8(v___x_2713_, 4);
v_unificationHints_2719_ = lean_ctor_get_uint8(v___x_2713_, 5);
v_proofIrrelevance_2720_ = lean_ctor_get_uint8(v___x_2713_, 6);
v_assignSyntheticOpaque_2721_ = lean_ctor_get_uint8(v___x_2713_, 7);
v_offsetCnstrs_2722_ = lean_ctor_get_uint8(v___x_2713_, 8);
v_transparency_2723_ = lean_ctor_get_uint8(v___x_2713_, 9);
v_univApprox_2724_ = lean_ctor_get_uint8(v___x_2713_, 11);
v_zetaUnused_2725_ = lean_ctor_get_uint8(v___x_2713_, 17);
v_canUnfoldPredicateConfig_2726_ = lean_ctor_get_uint8(v___x_2713_, 19);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2728_ = v___x_2713_;
v_isShared_2729_ = v_isSharedCheck_2757_;
goto v_resetjp_2727_;
}
else
{
lean_dec(v___x_2713_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2757_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
uint8_t v___x_2730_; uint8_t v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2734_; 
v___x_2730_ = 1;
v___x_2731_ = 0;
v___x_2732_ = 2;
if (v_isShared_2729_ == 0)
{
v___x_2734_ = v___x_2728_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 0, v_foApprox_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 1, v_ctxApprox_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 2, v_quasiPatternApprox_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 3, v_constApprox_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 4, v_isDefEqStuckEx_2718_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 5, v_unificationHints_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 6, v_proofIrrelevance_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 7, v_assignSyntheticOpaque_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 8, v_offsetCnstrs_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 9, v_transparency_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 11, v_univApprox_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 17, v_zetaUnused_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, 19, v_canUnfoldPredicateConfig_2726_);
v___x_2734_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
uint8_t v_trackZetaDelta_2735_; lean_object* v_zetaDeltaSet_2736_; lean_object* v_lctx_2737_; lean_object* v_localInstances_2738_; lean_object* v_defEqCtx_x3f_2739_; lean_object* v_synthPendingDepth_2740_; lean_object* v_customCanUnfoldPredicate_x3f_2741_; uint8_t v_univApprox_2742_; uint8_t v_inTypeClassResolution_2743_; uint8_t v_cacheInferType_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2754_; 
lean_ctor_set_uint8(v___x_2734_, 10, v___x_2731_);
lean_ctor_set_uint8(v___x_2734_, 12, v___x_2730_);
lean_ctor_set_uint8(v___x_2734_, 13, v___x_2730_);
lean_ctor_set_uint8(v___x_2734_, 14, v___x_2732_);
lean_ctor_set_uint8(v___x_2734_, 15, v___x_2730_);
lean_ctor_set_uint8(v___x_2734_, 16, v___x_2730_);
lean_ctor_set_uint8(v___x_2734_, 18, v___x_2730_);
v_trackZetaDelta_2735_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*7);
v_zetaDeltaSet_2736_ = lean_ctor_get(v___y_2707_, 1);
v_lctx_2737_ = lean_ctor_get(v___y_2707_, 2);
v_localInstances_2738_ = lean_ctor_get(v___y_2707_, 3);
v_defEqCtx_x3f_2739_ = lean_ctor_get(v___y_2707_, 4);
v_synthPendingDepth_2740_ = lean_ctor_get(v___y_2707_, 5);
v_customCanUnfoldPredicate_x3f_2741_ = lean_ctor_get(v___y_2707_, 6);
v_univApprox_2742_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2743_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*7 + 2);
v_cacheInferType_2744_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*7 + 3);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___y_2707_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v___y_2707_, 0);
lean_dec(v_unused_2755_);
v___x_2746_ = v___y_2707_;
v_isShared_2747_ = v_isSharedCheck_2754_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2741_);
lean_inc(v_synthPendingDepth_2740_);
lean_inc(v_defEqCtx_x3f_2739_);
lean_inc(v_localInstances_2738_);
lean_inc(v_lctx_2737_);
lean_inc(v_zetaDeltaSet_2736_);
lean_dec(v___y_2707_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2754_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint64_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2748_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2734_);
v___x_2749_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2749_, 0, v___x_2734_);
lean_ctor_set_uint64(v___x_2749_, sizeof(void*)*1, v___x_2748_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2749_);
v___x_2751_ = v___x_2746_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_zetaDeltaSet_2736_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_lctx_2737_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_localInstances_2738_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_defEqCtx_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2753_, 5, v_synthPendingDepth_2740_);
lean_ctor_set(v_reuseFailAlloc_2753_, 6, v_customCanUnfoldPredicate_x3f_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*7, v_trackZetaDelta_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*7 + 1, v_univApprox_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*7 + 3, v_cacheInferType_2744_);
v___x_2751_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_apply_5(v_x_2706_, v___x_2751_, v___y_2708_, v___y_2709_, v___y_2710_, lean_box(0));
return v___x_2752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___y_2787_; lean_object* v___x_2804_; uint8_t v_transparency_2805_; uint8_t v___x_2806_; uint8_t v___x_2807_; 
v___x_2804_ = l_Lean_Meta_Context_config(v_a_2781_);
v_transparency_2805_ = lean_ctor_get_uint8(v___x_2804_, 9);
lean_dec_ref(v___x_2804_);
v___x_2806_ = 1;
v___x_2807_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2805_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
v___x_2808_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
v___y_2787_ = v___x_2808_;
goto v___jp_2786_;
}
else
{
lean_object* v_keyedConfig_2809_; uint8_t v_trackZetaDelta_2810_; lean_object* v_zetaDeltaSet_2811_; lean_object* v_lctx_2812_; lean_object* v_localInstances_2813_; lean_object* v_defEqCtx_x3f_2814_; lean_object* v_synthPendingDepth_2815_; lean_object* v_customCanUnfoldPredicate_x3f_2816_; uint8_t v_univApprox_2817_; uint8_t v_inTypeClassResolution_2818_; uint8_t v_cacheInferType_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_keyedConfig_2809_ = lean_ctor_get(v_a_2781_, 0);
v_trackZetaDelta_2810_ = lean_ctor_get_uint8(v_a_2781_, sizeof(void*)*7);
v_zetaDeltaSet_2811_ = lean_ctor_get(v_a_2781_, 1);
v_lctx_2812_ = lean_ctor_get(v_a_2781_, 2);
v_localInstances_2813_ = lean_ctor_get(v_a_2781_, 3);
v_defEqCtx_x3f_2814_ = lean_ctor_get(v_a_2781_, 4);
v_synthPendingDepth_2815_ = lean_ctor_get(v_a_2781_, 5);
v_customCanUnfoldPredicate_x3f_2816_ = lean_ctor_get(v_a_2781_, 6);
v_univApprox_2817_ = lean_ctor_get_uint8(v_a_2781_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2818_ = lean_ctor_get_uint8(v_a_2781_, sizeof(void*)*7 + 2);
v_cacheInferType_2819_ = lean_ctor_get_uint8(v_a_2781_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2809_);
v___x_2820_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2806_, v_keyedConfig_2809_);
lean_inc(v_customCanUnfoldPredicate_x3f_2816_);
lean_inc(v_synthPendingDepth_2815_);
lean_inc(v_defEqCtx_x3f_2814_);
lean_inc_ref(v_localInstances_2813_);
lean_inc_ref(v_lctx_2812_);
lean_inc(v_zetaDeltaSet_2811_);
v___x_2821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v_zetaDeltaSet_2811_);
lean_ctor_set(v___x_2821_, 2, v_lctx_2812_);
lean_ctor_set(v___x_2821_, 3, v_localInstances_2813_);
lean_ctor_set(v___x_2821_, 4, v_defEqCtx_x3f_2814_);
lean_ctor_set(v___x_2821_, 5, v_synthPendingDepth_2815_);
lean_ctor_set(v___x_2821_, 6, v_customCanUnfoldPredicate_x3f_2816_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7, v_trackZetaDelta_2810_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 1, v_univApprox_2817_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2818_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 3, v_cacheInferType_2819_);
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
v___x_2822_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2780_, v___x_2821_, v_a_2782_, v_a_2783_, v_a_2784_);
v___y_2787_ = v___x_2822_;
goto v___jp_2786_;
}
v___jp_2786_:
{
if (lean_obj_tag(v___y_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_a_2788_ = lean_ctor_get(v___y_2787_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___y_2787_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___y_2787_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___y_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_a_2796_ = lean_ctor_get(v___y_2787_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___y_2787_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___y_2787_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___y_2787_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2830_, lean_object* v_x_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v___y_2838_; lean_object* v___x_2855_; uint8_t v_transparency_2856_; uint8_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = l_Lean_Meta_Context_config(v_a_2832_);
v_transparency_2856_ = lean_ctor_get_uint8(v___x_2855_, 9);
lean_dec_ref(v___x_2855_);
v___x_2857_ = 1;
v___x_2858_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_inc(v_a_2835_);
lean_inc_ref(v_a_2834_);
lean_inc(v_a_2833_);
lean_inc_ref(v_a_2832_);
v___x_2859_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
v___y_2838_ = v___x_2859_;
goto v___jp_2837_;
}
else
{
lean_object* v_keyedConfig_2860_; uint8_t v_trackZetaDelta_2861_; lean_object* v_zetaDeltaSet_2862_; lean_object* v_lctx_2863_; lean_object* v_localInstances_2864_; lean_object* v_defEqCtx_x3f_2865_; lean_object* v_synthPendingDepth_2866_; lean_object* v_customCanUnfoldPredicate_x3f_2867_; uint8_t v_univApprox_2868_; uint8_t v_inTypeClassResolution_2869_; uint8_t v_cacheInferType_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_keyedConfig_2860_ = lean_ctor_get(v_a_2832_, 0);
v_trackZetaDelta_2861_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*7);
v_zetaDeltaSet_2862_ = lean_ctor_get(v_a_2832_, 1);
v_lctx_2863_ = lean_ctor_get(v_a_2832_, 2);
v_localInstances_2864_ = lean_ctor_get(v_a_2832_, 3);
v_defEqCtx_x3f_2865_ = lean_ctor_get(v_a_2832_, 4);
v_synthPendingDepth_2866_ = lean_ctor_get(v_a_2832_, 5);
v_customCanUnfoldPredicate_x3f_2867_ = lean_ctor_get(v_a_2832_, 6);
v_univApprox_2868_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2869_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*7 + 2);
v_cacheInferType_2870_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2860_);
v___x_2871_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2857_, v_keyedConfig_2860_);
lean_inc(v_customCanUnfoldPredicate_x3f_2867_);
lean_inc(v_synthPendingDepth_2866_);
lean_inc(v_defEqCtx_x3f_2865_);
lean_inc_ref(v_localInstances_2864_);
lean_inc_ref(v_lctx_2863_);
lean_inc(v_zetaDeltaSet_2862_);
v___x_2872_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v_zetaDeltaSet_2862_);
lean_ctor_set(v___x_2872_, 2, v_lctx_2863_);
lean_ctor_set(v___x_2872_, 3, v_localInstances_2864_);
lean_ctor_set(v___x_2872_, 4, v_defEqCtx_x3f_2865_);
lean_ctor_set(v___x_2872_, 5, v_synthPendingDepth_2866_);
lean_ctor_set(v___x_2872_, 6, v_customCanUnfoldPredicate_x3f_2867_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*7, v_trackZetaDelta_2861_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*7 + 1, v_univApprox_2868_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2869_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*7 + 3, v_cacheInferType_2870_);
lean_inc(v_a_2835_);
lean_inc_ref(v_a_2834_);
lean_inc(v_a_2833_);
v___x_2873_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2831_, v___x_2872_, v_a_2833_, v_a_2834_, v_a_2835_);
v___y_2838_ = v___x_2873_;
goto v___jp_2837_;
}
v___jp_2837_:
{
if (lean_obj_tag(v___y_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
v_a_2839_ = lean_ctor_get(v___y_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___y_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___y_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___y_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v___y_2838_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___y_2838_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___y_2838_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___y_2838_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2874_, lean_object* v_x_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2874_, v_x_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
return v_res_2881_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = l_Lean_interruptExceptionId;
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v___x_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_ks_2904_; lean_object* v_vs_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2937_; 
v_ks_2904_ = lean_ctor_get(v_x_2900_, 0);
v_vs_2905_ = lean_ctor_get(v_x_2900_, 1);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2900_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2907_ = v_x_2900_;
v_isShared_2908_ = v_isSharedCheck_2937_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_vs_2905_);
lean_inc(v_ks_2904_);
lean_dec(v_x_2900_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2937_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = lean_array_get_size(v_ks_2904_);
v___x_2910_ = lean_nat_dec_lt(v_x_2901_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
lean_dec(v_x_2901_);
v___x_2911_ = lean_array_push(v_ks_2904_, v_x_2902_);
v___x_2912_ = lean_array_push(v_vs_2905_, v_x_2903_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2912_);
lean_ctor_set(v___x_2907_, 0, v___x_2911_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
else
{
lean_object* v_expr_2916_; uint64_t v_configKey_2917_; lean_object* v_k_x27_2918_; lean_object* v_expr_2919_; uint64_t v_configKey_2920_; uint64_t v___x_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint8_t v___x_2925_; 
v_expr_2916_ = lean_ctor_get(v_x_2902_, 0);
v_configKey_2917_ = lean_ctor_get_uint64(v_x_2902_, sizeof(void*)*1);
v_k_x27_2918_ = lean_array_fget_borrowed(v_ks_2904_, v_x_2901_);
v_expr_2919_ = lean_ctor_get(v_k_x27_2918_, 0);
v_configKey_2920_ = lean_ctor_get_uint64(v_k_x27_2918_, sizeof(void*)*1);
v___x_2921_ = l_Lean_Expr_hash(v_expr_2916_);
v___x_2922_ = lean_uint64_mix_hash(v___x_2921_, v_configKey_2917_);
v___x_2923_ = l_Lean_Expr_hash(v_expr_2919_);
v___x_2924_ = lean_uint64_mix_hash(v___x_2923_, v_configKey_2920_);
v___x_2925_ = lean_uint64_dec_eq(v___x_2922_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2927_; 
if (v_isShared_2908_ == 0)
{
v___x_2927_ = v___x_2907_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_ks_2904_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_vs_2905_);
v___x_2927_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_add(v_x_2901_, v___x_2928_);
lean_dec(v_x_2901_);
v_x_2900_ = v___x_2927_;
v_x_2901_ = v___x_2929_;
goto _start;
}
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2932_ = lean_array_fset(v_ks_2904_, v_x_2901_, v_x_2902_);
v___x_2933_ = lean_array_fset(v_vs_2905_, v_x_2901_, v_x_2903_);
lean_dec(v_x_2901_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2933_);
lean_ctor_set(v___x_2907_, 0, v___x_2932_);
v___x_2935_ = v___x_2907_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2938_, lean_object* v_k_2939_, lean_object* v_v_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_n_2938_, v___x_2941_, v_k_2939_, v_v_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2943_, size_t v_x_2944_, size_t v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_es_2948_; size_t v___x_2949_; size_t v___x_2950_; lean_object* v_j_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_es_2948_ = lean_ctor_get(v_x_2943_, 0);
v___x_2949_ = ((size_t)31ULL);
v___x_2950_ = lean_usize_land(v_x_2944_, v___x_2949_);
v_j_2951_ = lean_usize_to_nat(v___x_2950_);
v___x_2952_ = lean_array_get_size(v_es_2948_);
v___x_2953_ = lean_nat_dec_lt(v_j_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec(v_j_2951_);
lean_dec(v_x_2947_);
lean_dec_ref(v_x_2946_);
return v_x_2943_;
}
else
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3000_; 
lean_inc_ref(v_es_2948_);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_x_2943_, 0);
lean_dec(v_unused_3001_);
v___x_2955_ = v_x_2943_;
v_isShared_2956_ = v_isSharedCheck_3000_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_x_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3000_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_v_2957_; lean_object* v___x_2958_; lean_object* v_xs_x27_2959_; lean_object* v___y_2961_; 
v_v_2957_ = lean_array_fget(v_es_2948_, v_j_2951_);
v___x_2958_ = lean_box(0);
v_xs_x27_2959_ = lean_array_fset(v_es_2948_, v_j_2951_, v___x_2958_);
switch(lean_obj_tag(v_v_2957_))
{
case 0:
{
lean_object* v_key_2966_; lean_object* v_val_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2985_; 
v_key_2966_ = lean_ctor_get(v_v_2957_, 0);
v_val_2967_ = lean_ctor_get(v_v_2957_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_v_2957_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2969_ = v_v_2957_;
v_isShared_2970_ = v_isSharedCheck_2985_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_val_2967_);
lean_inc(v_key_2966_);
lean_dec(v_v_2957_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2985_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_expr_2971_; uint64_t v_configKey_2972_; lean_object* v_expr_2973_; uint64_t v_configKey_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; uint8_t v___x_2979_; 
v_expr_2971_ = lean_ctor_get(v_x_2946_, 0);
v_configKey_2972_ = lean_ctor_get_uint64(v_x_2946_, sizeof(void*)*1);
v_expr_2973_ = lean_ctor_get(v_key_2966_, 0);
v_configKey_2974_ = lean_ctor_get_uint64(v_key_2966_, sizeof(void*)*1);
v___x_2975_ = l_Lean_Expr_hash(v_expr_2971_);
v___x_2976_ = lean_uint64_mix_hash(v___x_2975_, v_configKey_2972_);
v___x_2977_ = l_Lean_Expr_hash(v_expr_2973_);
v___x_2978_ = lean_uint64_mix_hash(v___x_2977_, v_configKey_2974_);
v___x_2979_ = lean_uint64_dec_eq(v___x_2976_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_del_object(v___x_2969_);
v___x_2980_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2966_, v_val_2967_, v_x_2946_, v_x_2947_);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
v___y_2961_ = v___x_2981_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2983_; 
lean_dec(v_val_2967_);
lean_dec(v_key_2966_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v_x_2947_);
lean_ctor_set(v___x_2969_, 0, v_x_2946_);
v___x_2983_ = v___x_2969_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_x_2946_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_x_2947_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v___y_2961_ = v___x_2983_;
goto v___jp_2960_;
}
}
}
}
case 1:
{
lean_object* v_node_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2998_; 
v_node_2986_ = lean_ctor_get(v_v_2957_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_v_2957_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2988_ = v_v_2957_;
v_isShared_2989_ = v_isSharedCheck_2998_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_node_2986_);
lean_dec(v_v_2957_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2998_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
size_t v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2990_ = ((size_t)5ULL);
v___x_2991_ = lean_usize_shift_right(v_x_2944_, v___x_2990_);
v___x_2992_ = ((size_t)1ULL);
v___x_2993_ = lean_usize_add(v_x_2945_, v___x_2992_);
v___x_2994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2986_, v___x_2991_, v___x_2993_, v_x_2946_, v_x_2947_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2994_);
v___x_2996_ = v___x_2988_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
v___y_2961_ = v___x_2996_;
goto v___jp_2960_;
}
}
}
default: 
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_x_2946_);
lean_ctor_set(v___x_2999_, 1, v_x_2947_);
v___y_2961_ = v___x_2999_;
goto v___jp_2960_;
}
}
v___jp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = lean_array_fset(v_xs_x27_2959_, v_j_2951_, v___y_2961_);
lean_dec(v_j_2951_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2962_);
v___x_2964_ = v___x_2955_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v_ks_3002_; lean_object* v_vs_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3021_; 
v_ks_3002_ = lean_ctor_get(v_x_2943_, 0);
v_vs_3003_ = lean_ctor_get(v_x_2943_, 1);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3005_ = v_x_2943_;
v_isShared_3006_ = v_isSharedCheck_3021_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_vs_3003_);
lean_inc(v_ks_3002_);
lean_dec(v_x_2943_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3021_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_ks_3002_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_vs_3003_);
v___x_3008_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v_newNode_3009_; size_t v___x_3010_; uint8_t v___x_3011_; 
v_newNode_3009_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3008_, v_x_2946_, v_x_2947_);
v___x_3010_ = ((size_t)7ULL);
v___x_3011_ = lean_usize_dec_le(v___x_3010_, v_x_2945_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3009_);
v___x_3013_ = lean_unsigned_to_nat(4u);
v___x_3014_ = lean_nat_dec_lt(v___x_3012_, v___x_3013_);
lean_dec(v___x_3012_);
if (v___x_3014_ == 0)
{
lean_object* v_ks_3015_; lean_object* v_vs_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_ks_3015_ = lean_ctor_get(v_newNode_3009_, 0);
lean_inc_ref(v_ks_3015_);
v_vs_3016_ = lean_ctor_get(v_newNode_3009_, 1);
lean_inc_ref(v_vs_3016_);
lean_dec_ref(v_newNode_3009_);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3019_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2945_, v_ks_3015_, v_vs_3016_, v___x_3017_, v___x_3018_);
lean_dec_ref(v_vs_3016_);
lean_dec_ref(v_ks_3015_);
return v___x_3019_;
}
else
{
return v_newNode_3009_;
}
}
else
{
return v_newNode_3009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3022_, lean_object* v_keys_3023_, lean_object* v_vals_3024_, lean_object* v_i_3025_, lean_object* v_entries_3026_){
_start:
{
lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = lean_array_get_size(v_keys_3023_);
v___x_3028_ = lean_nat_dec_lt(v_i_3025_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v_i_3025_);
return v_entries_3026_;
}
else
{
lean_object* v_k_3029_; lean_object* v_expr_3030_; uint64_t v_configKey_3031_; lean_object* v_v_3032_; uint64_t v___x_3033_; uint64_t v___x_3034_; size_t v_h_3035_; size_t v___x_3036_; lean_object* v___x_3037_; size_t v___x_3038_; size_t v___x_3039_; size_t v___x_3040_; size_t v_h_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_k_3029_ = lean_array_fget_borrowed(v_keys_3023_, v_i_3025_);
v_expr_3030_ = lean_ctor_get(v_k_3029_, 0);
v_configKey_3031_ = lean_ctor_get_uint64(v_k_3029_, sizeof(void*)*1);
v_v_3032_ = lean_array_fget_borrowed(v_vals_3024_, v_i_3025_);
v___x_3033_ = l_Lean_Expr_hash(v_expr_3030_);
v___x_3034_ = lean_uint64_mix_hash(v___x_3033_, v_configKey_3031_);
v_h_3035_ = lean_uint64_to_usize(v___x_3034_);
v___x_3036_ = ((size_t)5ULL);
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = ((size_t)1ULL);
v___x_3039_ = lean_usize_sub(v_depth_3022_, v___x_3038_);
v___x_3040_ = lean_usize_mul(v___x_3036_, v___x_3039_);
v_h_3041_ = lean_usize_shift_right(v_h_3035_, v___x_3040_);
v___x_3042_ = lean_nat_add(v_i_3025_, v___x_3037_);
lean_dec(v_i_3025_);
lean_inc(v_v_3032_);
lean_inc(v_k_3029_);
v___x_3043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3026_, v_h_3041_, v_depth_3022_, v_k_3029_, v_v_3032_);
v_i_3025_ = v___x_3042_;
v_entries_3026_ = v___x_3043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3045_, lean_object* v_keys_3046_, lean_object* v_vals_3047_, lean_object* v_i_3048_, lean_object* v_entries_3049_){
_start:
{
size_t v_depth_boxed_3050_; lean_object* v_res_3051_; 
v_depth_boxed_3050_ = lean_unbox_usize(v_depth_3045_);
lean_dec(v_depth_3045_);
v_res_3051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3050_, v_keys_3046_, v_vals_3047_, v_i_3048_, v_entries_3049_);
lean_dec_ref(v_vals_3047_);
lean_dec_ref(v_keys_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_, lean_object* v_x_3055_, lean_object* v_x_3056_){
_start:
{
size_t v_x_3776__boxed_3057_; size_t v_x_3777__boxed_3058_; lean_object* v_res_3059_; 
v_x_3776__boxed_3057_ = lean_unbox_usize(v_x_3053_);
lean_dec(v_x_3053_);
v_x_3777__boxed_3058_ = lean_unbox_usize(v_x_3054_);
lean_dec(v_x_3054_);
v_res_3059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3052_, v_x_3776__boxed_3057_, v_x_3777__boxed_3058_, v_x_3055_, v_x_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
lean_object* v_expr_3063_; uint64_t v_configKey_3064_; uint64_t v___x_3065_; uint64_t v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v_expr_3063_ = lean_ctor_get(v_x_3061_, 0);
v_configKey_3064_ = lean_ctor_get_uint64(v_x_3061_, sizeof(void*)*1);
v___x_3065_ = l_Lean_Expr_hash(v_expr_3063_);
v___x_3066_ = lean_uint64_mix_hash(v___x_3065_, v_configKey_3064_);
v___x_3067_ = lean_uint64_to_usize(v___x_3066_);
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3060_, v___x_3067_, v___x_3068_, v_x_3061_, v_x_3062_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3070_, lean_object* v_vals_3071_, lean_object* v_i_3072_, lean_object* v_k_3073_){
_start:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = lean_array_get_size(v_keys_3070_);
v___x_3075_ = lean_nat_dec_lt(v_i_3072_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
lean_dec(v_i_3072_);
v___x_3076_ = lean_box(0);
return v___x_3076_;
}
else
{
lean_object* v_expr_3077_; uint64_t v_configKey_3078_; lean_object* v_k_x27_3079_; lean_object* v_expr_3080_; uint64_t v_configKey_3081_; uint64_t v___x_3082_; uint64_t v___x_3083_; uint64_t v___x_3084_; uint64_t v___x_3085_; uint8_t v___x_3086_; 
v_expr_3077_ = lean_ctor_get(v_k_3073_, 0);
v_configKey_3078_ = lean_ctor_get_uint64(v_k_3073_, sizeof(void*)*1);
v_k_x27_3079_ = lean_array_fget_borrowed(v_keys_3070_, v_i_3072_);
v_expr_3080_ = lean_ctor_get(v_k_x27_3079_, 0);
v_configKey_3081_ = lean_ctor_get_uint64(v_k_x27_3079_, sizeof(void*)*1);
v___x_3082_ = l_Lean_Expr_hash(v_expr_3077_);
v___x_3083_ = lean_uint64_mix_hash(v___x_3082_, v_configKey_3078_);
v___x_3084_ = l_Lean_Expr_hash(v_expr_3080_);
v___x_3085_ = lean_uint64_mix_hash(v___x_3084_, v_configKey_3081_);
v___x_3086_ = lean_uint64_dec_eq(v___x_3083_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_add(v_i_3072_, v___x_3087_);
lean_dec(v_i_3072_);
v_i_3072_ = v___x_3088_;
goto _start;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_array_fget_borrowed(v_vals_3071_, v_i_3072_);
lean_dec(v_i_3072_);
lean_inc(v___x_3090_);
lean_inc(v_k_x27_3079_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v_k_x27_3079_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
return v___x_3092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3093_, lean_object* v_vals_3094_, lean_object* v_i_3095_, lean_object* v_k_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3093_, v_vals_3094_, v_i_3095_, v_k_3096_);
lean_dec_ref(v_k_3096_);
lean_dec_ref(v_vals_3094_);
lean_dec_ref(v_keys_3093_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3098_, size_t v_x_3099_, lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
lean_object* v_es_3101_; lean_object* v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; lean_object* v_j_3105_; lean_object* v___x_3106_; 
v_es_3101_ = lean_ctor_get(v_x_3098_, 0);
v___x_3102_ = lean_box(2);
v___x_3103_ = ((size_t)31ULL);
v___x_3104_ = lean_usize_land(v_x_3099_, v___x_3103_);
v_j_3105_ = lean_usize_to_nat(v___x_3104_);
v___x_3106_ = lean_array_get_borrowed(v___x_3102_, v_es_3101_, v_j_3105_);
lean_dec(v_j_3105_);
switch(lean_obj_tag(v___x_3106_))
{
case 0:
{
lean_object* v_key_3107_; lean_object* v_val_3108_; lean_object* v_expr_3109_; uint64_t v_configKey_3110_; lean_object* v_expr_3111_; uint64_t v_configKey_3112_; uint64_t v___x_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; uint8_t v___x_3117_; 
v_key_3107_ = lean_ctor_get(v___x_3106_, 0);
v_val_3108_ = lean_ctor_get(v___x_3106_, 1);
v_expr_3109_ = lean_ctor_get(v_x_3100_, 0);
v_configKey_3110_ = lean_ctor_get_uint64(v_x_3100_, sizeof(void*)*1);
v_expr_3111_ = lean_ctor_get(v_key_3107_, 0);
v_configKey_3112_ = lean_ctor_get_uint64(v_key_3107_, sizeof(void*)*1);
v___x_3113_ = l_Lean_Expr_hash(v_expr_3109_);
v___x_3114_ = lean_uint64_mix_hash(v___x_3113_, v_configKey_3110_);
v___x_3115_ = l_Lean_Expr_hash(v_expr_3111_);
v___x_3116_ = lean_uint64_mix_hash(v___x_3115_, v_configKey_3112_);
v___x_3117_ = lean_uint64_dec_eq(v___x_3114_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_box(0);
return v___x_3118_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_inc(v_val_3108_);
lean_inc(v_key_3107_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_key_3107_);
lean_ctor_set(v___x_3119_, 1, v_val_3108_);
v___x_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
case 1:
{
lean_object* v_node_3121_; size_t v___x_3122_; size_t v___x_3123_; 
v_node_3121_ = lean_ctor_get(v___x_3106_, 0);
v___x_3122_ = ((size_t)5ULL);
v___x_3123_ = lean_usize_shift_right(v_x_3099_, v___x_3122_);
v_x_3098_ = v_node_3121_;
v_x_3099_ = v___x_3123_;
goto _start;
}
default: 
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_box(0);
return v___x_3125_;
}
}
}
else
{
lean_object* v_ks_3126_; lean_object* v_vs_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_ks_3126_ = lean_ctor_get(v_x_3098_, 0);
v_vs_3127_ = lean_ctor_get(v_x_3098_, 1);
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3126_, v_vs_3127_, v___x_3128_, v_x_3100_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3130_, lean_object* v_x_3131_, lean_object* v_x_3132_){
_start:
{
size_t v_x_4002__boxed_3133_; lean_object* v_res_3134_; 
v_x_4002__boxed_3133_ = lean_unbox_usize(v_x_3131_);
lean_dec(v_x_3131_);
v_res_3134_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3130_, v_x_4002__boxed_3133_, v_x_3132_);
lean_dec_ref(v_x_3132_);
lean_dec_ref(v_x_3130_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3135_, lean_object* v_x_3136_){
_start:
{
lean_object* v_expr_3137_; uint64_t v_configKey_3138_; uint64_t v___x_3139_; uint64_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v_expr_3137_ = lean_ctor_get(v_x_3136_, 0);
v_configKey_3138_ = lean_ctor_get_uint64(v_x_3136_, sizeof(void*)*1);
v___x_3139_ = l_Lean_Expr_hash(v_expr_3137_);
v___x_3140_ = lean_uint64_mix_hash(v___x_3139_, v_configKey_3138_);
v___x_3141_ = lean_uint64_to_usize(v___x_3140_);
v___x_3142_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3135_, v___x_3141_, v_x_3136_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3143_, lean_object* v_x_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3143_, v_x_3144_);
lean_dec_ref(v_x_3144_);
lean_dec_ref(v_x_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(lean_object* v_xs_3146_, lean_object* v_v_3147_, lean_object* v_i_3148_){
_start:
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = lean_array_get_size(v_xs_3146_);
v___x_3150_ = lean_nat_dec_lt(v_i_3148_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
lean_dec(v_i_3148_);
v___x_3151_ = lean_box(0);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; lean_object* v_expr_3153_; uint64_t v_configKey_3154_; lean_object* v_expr_3155_; uint64_t v_configKey_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v___x_3159_; uint64_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3152_ = lean_array_fget_borrowed(v_xs_3146_, v_i_3148_);
v_expr_3153_ = lean_ctor_get(v___x_3152_, 0);
v_configKey_3154_ = lean_ctor_get_uint64(v___x_3152_, sizeof(void*)*1);
v_expr_3155_ = lean_ctor_get(v_v_3147_, 0);
v_configKey_3156_ = lean_ctor_get_uint64(v_v_3147_, sizeof(void*)*1);
v___x_3157_ = l_Lean_Expr_hash(v_expr_3153_);
v___x_3158_ = lean_uint64_mix_hash(v___x_3157_, v_configKey_3154_);
v___x_3159_ = l_Lean_Expr_hash(v_expr_3155_);
v___x_3160_ = lean_uint64_mix_hash(v___x_3159_, v_configKey_3156_);
v___x_3161_ = lean_uint64_dec_eq(v___x_3158_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = lean_nat_add(v_i_3148_, v___x_3162_);
lean_dec(v_i_3148_);
v_i_3148_ = v___x_3163_;
goto _start;
}
else
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_i_3148_);
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11___boxed(lean_object* v_xs_3166_, lean_object* v_v_3167_, lean_object* v_i_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3166_, v_v_3167_, v_i_3168_);
lean_dec_ref(v_v_3167_);
lean_dec_ref(v_xs_3166_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(lean_object* v_xs_3170_, lean_object* v_v_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3170_, v_v_3171_, v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9___boxed(lean_object* v_xs_3174_, lean_object* v_v_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_xs_3174_, v_v_3175_);
lean_dec_ref(v_v_3175_);
lean_dec_ref(v_xs_3174_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(lean_object* v_x_3177_, size_t v_x_3178_, lean_object* v_x_3179_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 0)
{
lean_object* v_es_3180_; lean_object* v___x_3181_; size_t v___x_3182_; size_t v___x_3183_; lean_object* v_j_3184_; lean_object* v_entry_3185_; 
v_es_3180_ = lean_ctor_get(v_x_3177_, 0);
v___x_3181_ = lean_box(2);
v___x_3182_ = ((size_t)31ULL);
v___x_3183_ = lean_usize_land(v_x_3178_, v___x_3182_);
v_j_3184_ = lean_usize_to_nat(v___x_3183_);
v_entry_3185_ = lean_array_get(v___x_3181_, v_es_3180_, v_j_3184_);
switch(lean_obj_tag(v_entry_3185_))
{
case 0:
{
lean_object* v_key_3186_; lean_object* v_expr_3187_; uint64_t v_configKey_3188_; lean_object* v_expr_3189_; uint64_t v_configKey_3190_; uint64_t v___x_3191_; uint64_t v___x_3192_; uint64_t v___x_3193_; uint64_t v___x_3194_; uint8_t v___x_3195_; 
v_key_3186_ = lean_ctor_get(v_entry_3185_, 0);
lean_inc(v_key_3186_);
lean_dec_ref_known(v_entry_3185_, 2);
v_expr_3187_ = lean_ctor_get(v_x_3179_, 0);
v_configKey_3188_ = lean_ctor_get_uint64(v_x_3179_, sizeof(void*)*1);
v_expr_3189_ = lean_ctor_get(v_key_3186_, 0);
lean_inc_ref(v_expr_3189_);
v_configKey_3190_ = lean_ctor_get_uint64(v_key_3186_, sizeof(void*)*1);
lean_dec(v_key_3186_);
v___x_3191_ = l_Lean_Expr_hash(v_expr_3187_);
v___x_3192_ = lean_uint64_mix_hash(v___x_3191_, v_configKey_3188_);
v___x_3193_ = l_Lean_Expr_hash(v_expr_3189_);
lean_dec_ref(v_expr_3189_);
v___x_3194_ = lean_uint64_mix_hash(v___x_3193_, v_configKey_3190_);
v___x_3195_ = lean_uint64_dec_eq(v___x_3192_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_dec(v_j_3184_);
return v_x_3177_;
}
else
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
lean_inc_ref(v_es_3180_);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v_x_3177_, 0);
lean_dec(v_unused_3204_);
v___x_3197_ = v_x_3177_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v_x_3177_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_array_set(v_es_3180_, v_j_3184_, v___x_3181_);
lean_dec(v_j_3184_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
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
case 1:
{
lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3239_; 
lean_inc_ref(v_es_3180_);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_x_3177_, 0);
lean_dec(v_unused_3240_);
v___x_3206_ = v_x_3177_;
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
else
{
lean_dec(v_x_3177_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v_node_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3238_; 
v_node_3208_ = lean_ctor_get(v_entry_3185_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_entry_3185_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3210_ = v_entry_3185_;
v_isShared_3211_ = v_isSharedCheck_3238_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_node_3208_);
lean_dec(v_entry_3185_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3238_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
size_t v___x_3212_; lean_object* v_entries_3213_; size_t v___x_3214_; lean_object* v_newNode_3215_; lean_object* v___x_3216_; 
v___x_3212_ = ((size_t)5ULL);
v_entries_3213_ = lean_array_set(v_es_3180_, v_j_3184_, v___x_3181_);
v___x_3214_ = lean_usize_shift_right(v_x_3178_, v___x_3212_);
v_newNode_3215_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_node_3208_, v___x_3214_, v_x_3179_);
lean_inc_ref(v_newNode_3215_);
v___x_3216_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3218_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v_newNode_3215_);
v___x_3218_ = v___x_3210_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_newNode_3215_);
v___x_3218_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_array_set(v_entries_3213_, v_j_3184_, v___x_3218_);
lean_dec(v_j_3184_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3219_);
v___x_3221_ = v___x_3206_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
else
{
lean_object* v_val_3224_; lean_object* v_fst_3225_; lean_object* v_snd_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_newNode_3215_);
lean_del_object(v___x_3210_);
v_val_3224_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v___x_3216_, 1);
v_fst_3225_ = lean_ctor_get(v_val_3224_, 0);
v_snd_3226_ = lean_ctor_get(v_val_3224_, 1);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_val_3224_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3228_ = v_val_3224_;
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_snd_3226_);
lean_inc(v_fst_3225_);
lean_dec(v_val_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_fst_3225_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_snd_3226_);
v___x_3231_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3232_ = lean_array_set(v_entries_3213_, v_j_3184_, v___x_3231_);
lean_dec(v_j_3184_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3232_);
v___x_3234_ = v___x_3206_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_3184_);
return v_x_3177_;
}
}
}
else
{
lean_object* v_ks_3241_; lean_object* v_vs_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3256_; 
v_ks_3241_ = lean_ctor_get(v_x_3177_, 0);
v_vs_3242_ = lean_ctor_get(v_x_3177_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3244_ = v_x_3177_;
v_isShared_3245_ = v_isSharedCheck_3256_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_vs_3242_);
lean_inc(v_ks_3241_);
lean_dec(v_x_3177_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3256_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_ks_3241_, v_x_3179_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v___x_3248_; 
if (v_isShared_3245_ == 0)
{
v___x_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_ks_3241_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_vs_3242_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
else
{
lean_object* v_val_3250_; lean_object* v_keys_x27_3251_; lean_object* v_vals_x27_3252_; lean_object* v___x_3254_; 
v_val_3250_ = lean_ctor_get(v___x_3246_, 0);
lean_inc_n(v_val_3250_, 2);
lean_dec_ref_known(v___x_3246_, 1);
v_keys_x27_3251_ = l_Array_eraseIdx___redArg(v_ks_3241_, v_val_3250_);
v_vals_x27_3252_ = l_Array_eraseIdx___redArg(v_vs_3242_, v_val_3250_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v_vals_x27_3252_);
lean_ctor_set(v___x_3244_, 0, v_keys_x27_3251_);
v___x_3254_ = v___x_3244_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_keys_x27_3251_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_vals_x27_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg___boxed(lean_object* v_x_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
size_t v_x_4123__boxed_3260_; lean_object* v_res_3261_; 
v_x_4123__boxed_3260_ = lean_unbox_usize(v_x_3258_);
lean_dec(v_x_3258_);
v_res_3261_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3257_, v_x_4123__boxed_3260_, v_x_3259_);
lean_dec_ref(v_x_3259_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v_expr_3264_; uint64_t v_configKey_3265_; uint64_t v___x_3266_; uint64_t v___x_3267_; size_t v_h_3268_; lean_object* v___x_3269_; 
v_expr_3264_ = lean_ctor_get(v_x_3263_, 0);
v_configKey_3265_ = lean_ctor_get_uint64(v_x_3263_, sizeof(void*)*1);
v___x_3266_ = l_Lean_Expr_hash(v_expr_3264_);
v___x_3267_ = lean_uint64_mix_hash(v___x_3266_, v_configKey_3265_);
v_h_3268_ = lean_uint64_to_usize(v___x_3267_);
v___x_3269_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3262_, v_h_3268_, v_x_3263_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg___boxed(lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3270_, v_x_3271_);
lean_dec_ref(v_x_3271_);
return v_res_3272_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
switch(lean_obj_tag(v_e_3276_))
{
case 0:
{
lean_object* v_deBruijnIndex_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_deBruijnIndex_3314_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_deBruijnIndex_3314_);
lean_dec_ref_known(v_e_3276_, 1);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3316_ = l_Lean_mkBVar(v_deBruijnIndex_3314_);
v___x_3317_ = l_Lean_MessageData_ofExpr(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3315_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3318_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3319_;
}
case 1:
{
lean_object* v_fvarId_3320_; lean_object* v___x_3321_; 
v_fvarId_3320_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_fvarId_3320_);
lean_dec_ref_known(v_e_3276_, 1);
v___x_3321_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3320_, v_a_3277_, v_a_3279_, v_a_3280_);
return v___x_3321_;
}
case 2:
{
lean_object* v_mvarId_3322_; lean_object* v___x_3323_; 
v_mvarId_3322_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_mvarId_3322_);
lean_dec_ref_known(v_e_3276_, 1);
v___x_3323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3322_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3323_;
}
case 3:
{
lean_object* v_u_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_u_3324_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_u_3324_);
lean_dec_ref_known(v_e_3276_, 1);
v___x_3325_ = l_Lean_Level_succ___override(v_u_3324_);
v___x_3326_ = l_Lean_mkSort(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
case 4:
{
lean_object* v_declName_3328_; lean_object* v_us_3329_; 
v_declName_3328_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_declName_3328_);
v_us_3329_ = lean_ctor_get(v_e_3276_, 1);
lean_inc(v_us_3329_);
if (lean_obj_tag(v_us_3329_) == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref_known(v_e_3276_, 2);
v___x_3346_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3328_, v_us_3329_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3346_;
}
else
{
uint8_t v_cacheInferType_3347_; 
v_cacheInferType_3347_ = lean_ctor_get_uint8(v_a_3277_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3347_ == 0)
{
lean_dec_ref_known(v_e_3276_, 2);
goto v___jp_3330_;
}
else
{
uint8_t v___x_3348_; 
v___x_3348_ = l_Lean_Expr_hasMVar(v_e_3276_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3457_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3457_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3457_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3410_; lean_object* v_cache_3411_; lean_object* v_inferType_3412_; lean_object* v___x_3413_; 
v___x_3410_ = lean_st_ref_get(v_a_3278_);
v_cache_3411_ = lean_ctor_get(v___x_3410_, 1);
lean_inc_ref(v_cache_3411_);
lean_dec(v___x_3410_);
v_inferType_3412_ = lean_ctor_get(v_cache_3411_, 0);
lean_inc_ref(v_inferType_3412_);
lean_dec_ref(v_cache_3411_);
v___x_3413_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3412_, v_a_3350_);
if (lean_obj_tag(v___x_3413_) == 1)
{
lean_object* v_val_3414_; lean_object* v_fst_3415_; lean_object* v_snd_3416_; lean_object* v_expr_3417_; uint64_t v_configKey_3418_; lean_object* v_expr_3419_; uint64_t v_configKey_3420_; uint8_t v___x_3421_; 
v_val_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_val_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_fst_3415_ = lean_ctor_get(v_val_3414_, 0);
lean_inc(v_fst_3415_);
v_snd_3416_ = lean_ctor_get(v_val_3414_, 1);
lean_inc(v_snd_3416_);
lean_dec(v_val_3414_);
v_expr_3417_ = lean_ctor_get(v_a_3350_, 0);
v_configKey_3418_ = lean_ctor_get_uint64(v_a_3350_, sizeof(void*)*1);
v_expr_3419_ = lean_ctor_get(v_fst_3415_, 0);
lean_inc_ref(v_expr_3419_);
v_configKey_3420_ = lean_ctor_get_uint64(v_fst_3415_, sizeof(void*)*1);
lean_dec(v_fst_3415_);
v___x_3421_ = lean_uint64_dec_eq(v_configKey_3418_, v_configKey_3420_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v_expr_3419_);
lean_dec(v_snd_3416_);
lean_dec_ref(v_inferType_3412_);
lean_del_object(v___x_3352_);
goto v___jp_3396_;
}
else
{
size_t v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = ((size_t)64ULL);
v___x_3423_ = lean_expr_equal_budgeted(v_expr_3417_, v_expr_3419_, v___x_3422_);
lean_dec_ref(v_expr_3419_);
switch(v___x_3423_)
{
case 0:
{
lean_dec(v_snd_3416_);
lean_dec_ref(v_inferType_3412_);
lean_del_object(v___x_3352_);
goto v___jp_3396_;
}
case 1:
{
lean_object* v___x_3425_; 
lean_dec_ref(v_inferType_3412_);
lean_dec(v_a_3350_);
lean_dec(v_us_3329_);
lean_dec(v_declName_3328_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_snd_3416_);
v___x_3425_ = v___x_3352_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_snd_3416_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
default: 
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v_cache_3429_; lean_object* v_mctx_3430_; lean_object* v_zetaDeltaFVarIds_3431_; lean_object* v_postponed_3432_; lean_object* v_diag_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_snd_3416_);
lean_del_object(v___x_3352_);
v___x_3427_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3412_, v_a_3350_);
v___x_3428_ = lean_st_ref_take(v_a_3278_);
v_cache_3429_ = lean_ctor_get(v___x_3428_, 1);
v_mctx_3430_ = lean_ctor_get(v___x_3428_, 0);
v_zetaDeltaFVarIds_3431_ = lean_ctor_get(v___x_3428_, 2);
v_postponed_3432_ = lean_ctor_get(v___x_3428_, 3);
v_diag_3433_ = lean_ctor_get(v___x_3428_, 4);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3435_ = v___x_3428_;
v_isShared_3436_ = v_isSharedCheck_3456_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_diag_3433_);
lean_inc(v_postponed_3432_);
lean_inc(v_zetaDeltaFVarIds_3431_);
lean_inc(v_cache_3429_);
lean_inc(v_mctx_3430_);
lean_dec(v___x_3428_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3456_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_funInfo_3437_; lean_object* v_synthInstance_3438_; lean_object* v_whnf_3439_; lean_object* v_defEqTrans_3440_; lean_object* v_defEqPerm_3441_; lean_object* v_isUnitLike_3442_; lean_object* v_unfold_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3454_; 
v_funInfo_3437_ = lean_ctor_get(v_cache_3429_, 1);
v_synthInstance_3438_ = lean_ctor_get(v_cache_3429_, 2);
v_whnf_3439_ = lean_ctor_get(v_cache_3429_, 3);
v_defEqTrans_3440_ = lean_ctor_get(v_cache_3429_, 4);
v_defEqPerm_3441_ = lean_ctor_get(v_cache_3429_, 5);
v_isUnitLike_3442_ = lean_ctor_get(v_cache_3429_, 6);
v_unfold_3443_ = lean_ctor_get(v_cache_3429_, 7);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_cache_3429_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v_cache_3429_, 0);
lean_dec(v_unused_3455_);
v___x_3445_ = v_cache_3429_;
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_unfold_3443_);
lean_inc(v_isUnitLike_3442_);
lean_inc(v_defEqPerm_3441_);
lean_inc(v_defEqTrans_3440_);
lean_inc(v_whnf_3439_);
lean_inc(v_synthInstance_3438_);
lean_inc(v_funInfo_3437_);
lean_dec(v_cache_3429_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3454_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3427_);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_funInfo_3437_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_synthInstance_3438_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_whnf_3439_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_defEqTrans_3440_);
lean_ctor_set(v_reuseFailAlloc_3453_, 5, v_defEqPerm_3441_);
lean_ctor_set(v_reuseFailAlloc_3453_, 6, v_isUnitLike_3442_);
lean_ctor_set(v_reuseFailAlloc_3453_, 7, v_unfold_3443_);
v___x_3448_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3448_);
v___x_3450_ = v___x_3435_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_mctx_3430_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_zetaDeltaFVarIds_3431_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_postponed_3432_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_diag_3433_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_st_ref_put(v_a_3278_, v___x_3450_);
goto v___jp_3396_;
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
lean_dec(v___x_3413_);
lean_dec_ref(v_inferType_3412_);
lean_del_object(v___x_3352_);
goto v___jp_3396_;
}
v___jp_3354_:
{
lean_object* v___x_3355_; 
v___x_3355_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3328_, v_us_3329_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; uint8_t v___x_3357_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v___x_3357_ = l_Lean_Expr_hasMVar(v_a_3356_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3394_; 
lean_inc(v_a_3356_);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3355_, 0);
lean_dec(v_unused_3395_);
v___x_3359_ = v___x_3355_;
v_isShared_3360_ = v_isSharedCheck_3394_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3394_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v_cache_3362_; lean_object* v_mctx_3363_; lean_object* v_zetaDeltaFVarIds_3364_; lean_object* v_postponed_3365_; lean_object* v_diag_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3393_; 
v___x_3361_ = lean_st_ref_take(v_a_3278_);
v_cache_3362_ = lean_ctor_get(v___x_3361_, 1);
v_mctx_3363_ = lean_ctor_get(v___x_3361_, 0);
v_zetaDeltaFVarIds_3364_ = lean_ctor_get(v___x_3361_, 2);
v_postponed_3365_ = lean_ctor_get(v___x_3361_, 3);
v_diag_3366_ = lean_ctor_get(v___x_3361_, 4);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3368_ = v___x_3361_;
v_isShared_3369_ = v_isSharedCheck_3393_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_diag_3366_);
lean_inc(v_postponed_3365_);
lean_inc(v_zetaDeltaFVarIds_3364_);
lean_inc(v_cache_3362_);
lean_inc(v_mctx_3363_);
lean_dec(v___x_3361_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3393_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_inferType_3370_; lean_object* v_funInfo_3371_; lean_object* v_synthInstance_3372_; lean_object* v_whnf_3373_; lean_object* v_defEqTrans_3374_; lean_object* v_defEqPerm_3375_; lean_object* v_isUnitLike_3376_; lean_object* v_unfold_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3392_; 
v_inferType_3370_ = lean_ctor_get(v_cache_3362_, 0);
v_funInfo_3371_ = lean_ctor_get(v_cache_3362_, 1);
v_synthInstance_3372_ = lean_ctor_get(v_cache_3362_, 2);
v_whnf_3373_ = lean_ctor_get(v_cache_3362_, 3);
v_defEqTrans_3374_ = lean_ctor_get(v_cache_3362_, 4);
v_defEqPerm_3375_ = lean_ctor_get(v_cache_3362_, 5);
v_isUnitLike_3376_ = lean_ctor_get(v_cache_3362_, 6);
v_unfold_3377_ = lean_ctor_get(v_cache_3362_, 7);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_cache_3362_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3379_ = v_cache_3362_;
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_unfold_3377_);
lean_inc(v_isUnitLike_3376_);
lean_inc(v_defEqPerm_3375_);
lean_inc(v_defEqTrans_3374_);
lean_inc(v_whnf_3373_);
lean_inc(v_synthInstance_3372_);
lean_inc(v_funInfo_3371_);
lean_inc(v_inferType_3370_);
lean_dec(v_cache_3362_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_inc(v_a_3356_);
v___x_3381_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3370_, v_a_3350_, v_a_3356_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_funInfo_3371_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_synthInstance_3372_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v_whnf_3373_);
lean_ctor_set(v_reuseFailAlloc_3391_, 4, v_defEqTrans_3374_);
lean_ctor_set(v_reuseFailAlloc_3391_, 5, v_defEqPerm_3375_);
lean_ctor_set(v_reuseFailAlloc_3391_, 6, v_isUnitLike_3376_);
lean_ctor_set(v_reuseFailAlloc_3391_, 7, v_unfold_3377_);
v___x_3383_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3383_);
v___x_3385_ = v___x_3368_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_mctx_3363_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_zetaDeltaFVarIds_3364_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_postponed_3365_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_diag_3366_);
v___x_3385_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_st_ref_put(v_a_3278_, v___x_3385_);
if (v_isShared_3360_ == 0)
{
v___x_3388_ = v___x_3359_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3356_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3350_);
return v___x_3355_;
}
}
else
{
lean_dec(v_a_3350_);
return v___x_3355_;
}
}
v___jp_3396_:
{
lean_object* v_toCold_3397_; lean_object* v_cancelTk_x3f_3398_; 
v_toCold_3397_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3398_ = lean_ctor_get(v_toCold_3397_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3398_) == 1)
{
lean_object* v_val_3399_; uint8_t v___x_3400_; 
v_val_3399_ = lean_ctor_get(v_cancelTk_x3f_3398_, 0);
v___x_3400_ = l_IO_CancelToken_isSet(v_val_3399_);
if (v___x_3400_ == 0)
{
goto v___jp_3354_;
}
else
{
lean_object* v___x_3401_; lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_a_3350_);
lean_dec(v_us_3329_);
lean_dec(v_declName_3328_);
v___x_3401_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
goto v___jp_3354_;
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_us_3329_);
lean_dec(v_declName_3328_);
v_a_3458_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3349_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3349_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3276_, 2);
goto v___jp_3330_;
}
}
}
v___jp_3330_:
{
lean_object* v_toCold_3331_; lean_object* v_cancelTk_x3f_3332_; 
v_toCold_3331_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3332_ = lean_ctor_get(v_toCold_3331_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3332_) == 1)
{
lean_object* v_val_3333_; uint8_t v___x_3334_; 
v_val_3333_ = lean_ctor_get(v_cancelTk_x3f_3332_, 0);
v___x_3334_ = l_IO_CancelToken_isSet(v_val_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
v___x_3335_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3328_, v_us_3329_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_us_3329_);
lean_dec(v_declName_3328_);
v___x_3336_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v___x_3345_; 
v___x_3345_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3328_, v_us_3329_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3345_;
}
}
}
case 5:
{
lean_object* v_fn_3466_; uint8_t v_cacheInferType_3467_; lean_object* v_nargs_3468_; lean_object* v___x_3469_; lean_object* v_dummy_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_fn_3466_ = lean_ctor_get(v_e_3276_, 0);
v_cacheInferType_3467_ = lean_ctor_get_uint8(v_a_3277_, sizeof(void*)*7 + 3);
v_nargs_3468_ = l_Lean_Expr_getAppNumArgs(v_e_3276_);
v___x_3469_ = l_Lean_Expr_getAppFn(v_fn_3466_);
v_dummy_3470_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3468_);
v___x_3471_ = lean_mk_array(v_nargs_3468_, v_dummy_3470_);
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_sub(v_nargs_3468_, v___x_3472_);
lean_dec(v_nargs_3468_);
lean_inc_ref(v_e_3276_);
v___x_3474_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3276_, v___x_3471_, v___x_3473_);
if (v_cacheInferType_3467_ == 0)
{
lean_dec_ref_known(v_e_3276_, 2);
goto v___jp_3475_;
}
else
{
uint8_t v___x_3491_; 
v___x_3491_ = l_Lean_Expr_hasMVar(v_e_3276_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3600_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3600_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3600_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3553_; lean_object* v_cache_3554_; lean_object* v_inferType_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_st_ref_get(v_a_3278_);
v_cache_3554_ = lean_ctor_get(v___x_3553_, 1);
lean_inc_ref(v_cache_3554_);
lean_dec(v___x_3553_);
v_inferType_3555_ = lean_ctor_get(v_cache_3554_, 0);
lean_inc_ref(v_inferType_3555_);
lean_dec_ref(v_cache_3554_);
v___x_3556_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3555_, v_a_3493_);
if (lean_obj_tag(v___x_3556_) == 1)
{
lean_object* v_val_3557_; lean_object* v_fst_3558_; lean_object* v_snd_3559_; lean_object* v_expr_3560_; uint64_t v_configKey_3561_; lean_object* v_expr_3562_; uint64_t v_configKey_3563_; uint8_t v___x_3564_; 
v_val_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v_fst_3558_ = lean_ctor_get(v_val_3557_, 0);
lean_inc(v_fst_3558_);
v_snd_3559_ = lean_ctor_get(v_val_3557_, 1);
lean_inc(v_snd_3559_);
lean_dec(v_val_3557_);
v_expr_3560_ = lean_ctor_get(v_a_3493_, 0);
v_configKey_3561_ = lean_ctor_get_uint64(v_a_3493_, sizeof(void*)*1);
v_expr_3562_ = lean_ctor_get(v_fst_3558_, 0);
lean_inc_ref(v_expr_3562_);
v_configKey_3563_ = lean_ctor_get_uint64(v_fst_3558_, sizeof(void*)*1);
lean_dec(v_fst_3558_);
v___x_3564_ = lean_uint64_dec_eq(v_configKey_3561_, v_configKey_3563_);
if (v___x_3564_ == 0)
{
lean_dec_ref(v_expr_3562_);
lean_dec(v_snd_3559_);
lean_dec_ref(v_inferType_3555_);
lean_del_object(v___x_3495_);
goto v___jp_3539_;
}
else
{
size_t v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = ((size_t)64ULL);
v___x_3566_ = lean_expr_equal_budgeted(v_expr_3560_, v_expr_3562_, v___x_3565_);
lean_dec_ref(v_expr_3562_);
switch(v___x_3566_)
{
case 0:
{
lean_dec(v_snd_3559_);
lean_dec_ref(v_inferType_3555_);
lean_del_object(v___x_3495_);
goto v___jp_3539_;
}
case 1:
{
lean_object* v___x_3568_; 
lean_dec_ref(v_inferType_3555_);
lean_dec(v_a_3493_);
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3469_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v_snd_3559_);
v___x_3568_ = v___x_3495_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_snd_3559_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
default: 
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_cache_3572_; lean_object* v_mctx_3573_; lean_object* v_zetaDeltaFVarIds_3574_; lean_object* v_postponed_3575_; lean_object* v_diag_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v_snd_3559_);
lean_del_object(v___x_3495_);
v___x_3570_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3555_, v_a_3493_);
v___x_3571_ = lean_st_ref_take(v_a_3278_);
v_cache_3572_ = lean_ctor_get(v___x_3571_, 1);
v_mctx_3573_ = lean_ctor_get(v___x_3571_, 0);
v_zetaDeltaFVarIds_3574_ = lean_ctor_get(v___x_3571_, 2);
v_postponed_3575_ = lean_ctor_get(v___x_3571_, 3);
v_diag_3576_ = lean_ctor_get(v___x_3571_, 4);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3578_ = v___x_3571_;
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_diag_3576_);
lean_inc(v_postponed_3575_);
lean_inc(v_zetaDeltaFVarIds_3574_);
lean_inc(v_cache_3572_);
lean_inc(v_mctx_3573_);
lean_dec(v___x_3571_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_funInfo_3580_; lean_object* v_synthInstance_3581_; lean_object* v_whnf_3582_; lean_object* v_defEqTrans_3583_; lean_object* v_defEqPerm_3584_; lean_object* v_isUnitLike_3585_; lean_object* v_unfold_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3597_; 
v_funInfo_3580_ = lean_ctor_get(v_cache_3572_, 1);
v_synthInstance_3581_ = lean_ctor_get(v_cache_3572_, 2);
v_whnf_3582_ = lean_ctor_get(v_cache_3572_, 3);
v_defEqTrans_3583_ = lean_ctor_get(v_cache_3572_, 4);
v_defEqPerm_3584_ = lean_ctor_get(v_cache_3572_, 5);
v_isUnitLike_3585_ = lean_ctor_get(v_cache_3572_, 6);
v_unfold_3586_ = lean_ctor_get(v_cache_3572_, 7);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_cache_3572_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v_cache_3572_, 0);
lean_dec(v_unused_3598_);
v___x_3588_ = v_cache_3572_;
v_isShared_3589_ = v_isSharedCheck_3597_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_unfold_3586_);
lean_inc(v_isUnitLike_3585_);
lean_inc(v_defEqPerm_3584_);
lean_inc(v_defEqTrans_3583_);
lean_inc(v_whnf_3582_);
lean_inc(v_synthInstance_3581_);
lean_inc(v_funInfo_3580_);
lean_dec(v_cache_3572_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3597_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3570_);
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_funInfo_3580_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_synthInstance_3581_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_whnf_3582_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_defEqTrans_3583_);
lean_ctor_set(v_reuseFailAlloc_3596_, 5, v_defEqPerm_3584_);
lean_ctor_set(v_reuseFailAlloc_3596_, 6, v_isUnitLike_3585_);
lean_ctor_set(v_reuseFailAlloc_3596_, 7, v_unfold_3586_);
v___x_3591_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v___x_3591_);
v___x_3593_ = v___x_3578_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_mctx_3573_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_zetaDeltaFVarIds_3574_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_postponed_3575_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_diag_3576_);
v___x_3593_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; 
v___x_3594_ = lean_st_ref_put(v_a_3278_, v___x_3593_);
goto v___jp_3539_;
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
lean_dec(v___x_3556_);
lean_dec_ref(v_inferType_3555_);
lean_del_object(v___x_3495_);
goto v___jp_3539_;
}
v___jp_3497_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3469_, v___x_3474_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec_ref(v___x_3474_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; uint8_t v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v___x_3500_ = l_Lean_Expr_hasMVar(v_a_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3537_; 
lean_inc(v_a_3499_);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; 
v_unused_3538_ = lean_ctor_get(v___x_3498_, 0);
lean_dec(v_unused_3538_);
v___x_3502_ = v___x_3498_;
v_isShared_3503_ = v_isSharedCheck_3537_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v___x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3537_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v_cache_3505_; lean_object* v_mctx_3506_; lean_object* v_zetaDeltaFVarIds_3507_; lean_object* v_postponed_3508_; lean_object* v_diag_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3536_; 
v___x_3504_ = lean_st_ref_take(v_a_3278_);
v_cache_3505_ = lean_ctor_get(v___x_3504_, 1);
v_mctx_3506_ = lean_ctor_get(v___x_3504_, 0);
v_zetaDeltaFVarIds_3507_ = lean_ctor_get(v___x_3504_, 2);
v_postponed_3508_ = lean_ctor_get(v___x_3504_, 3);
v_diag_3509_ = lean_ctor_get(v___x_3504_, 4);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3511_ = v___x_3504_;
v_isShared_3512_ = v_isSharedCheck_3536_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_diag_3509_);
lean_inc(v_postponed_3508_);
lean_inc(v_zetaDeltaFVarIds_3507_);
lean_inc(v_cache_3505_);
lean_inc(v_mctx_3506_);
lean_dec(v___x_3504_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3536_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_inferType_3513_; lean_object* v_funInfo_3514_; lean_object* v_synthInstance_3515_; lean_object* v_whnf_3516_; lean_object* v_defEqTrans_3517_; lean_object* v_defEqPerm_3518_; lean_object* v_isUnitLike_3519_; lean_object* v_unfold_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3535_; 
v_inferType_3513_ = lean_ctor_get(v_cache_3505_, 0);
v_funInfo_3514_ = lean_ctor_get(v_cache_3505_, 1);
v_synthInstance_3515_ = lean_ctor_get(v_cache_3505_, 2);
v_whnf_3516_ = lean_ctor_get(v_cache_3505_, 3);
v_defEqTrans_3517_ = lean_ctor_get(v_cache_3505_, 4);
v_defEqPerm_3518_ = lean_ctor_get(v_cache_3505_, 5);
v_isUnitLike_3519_ = lean_ctor_get(v_cache_3505_, 6);
v_unfold_3520_ = lean_ctor_get(v_cache_3505_, 7);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_cache_3505_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3522_ = v_cache_3505_;
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_unfold_3520_);
lean_inc(v_isUnitLike_3519_);
lean_inc(v_defEqPerm_3518_);
lean_inc(v_defEqTrans_3517_);
lean_inc(v_whnf_3516_);
lean_inc(v_synthInstance_3515_);
lean_inc(v_funInfo_3514_);
lean_inc(v_inferType_3513_);
lean_dec(v_cache_3505_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3535_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_inc(v_a_3499_);
v___x_3524_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3513_, v_a_3493_, v_a_3499_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3524_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_funInfo_3514_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_synthInstance_3515_);
lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_whnf_3516_);
lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_defEqTrans_3517_);
lean_ctor_set(v_reuseFailAlloc_3534_, 5, v_defEqPerm_3518_);
lean_ctor_set(v_reuseFailAlloc_3534_, 6, v_isUnitLike_3519_);
lean_ctor_set(v_reuseFailAlloc_3534_, 7, v_unfold_3520_);
v___x_3526_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v___x_3526_);
v___x_3528_ = v___x_3511_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_mctx_3506_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_zetaDeltaFVarIds_3507_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_postponed_3508_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_diag_3509_);
v___x_3528_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_st_ref_put(v_a_3278_, v___x_3528_);
if (v_isShared_3503_ == 0)
{
v___x_3531_ = v___x_3502_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3499_);
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
}
}
}
else
{
lean_dec(v_a_3493_);
return v___x_3498_;
}
}
else
{
lean_dec(v_a_3493_);
return v___x_3498_;
}
}
v___jp_3539_:
{
lean_object* v_toCold_3540_; lean_object* v_cancelTk_x3f_3541_; 
v_toCold_3540_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3541_ = lean_ctor_get(v_toCold_3540_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3541_) == 1)
{
lean_object* v_val_3542_; uint8_t v___x_3543_; 
v_val_3542_ = lean_ctor_get(v_cancelTk_x3f_3541_, 0);
v___x_3543_ = l_IO_CancelToken_isSet(v_val_3542_);
if (v___x_3543_ == 0)
{
goto v___jp_3497_;
}
else
{
lean_object* v___x_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_a_3493_);
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3469_);
v___x_3544_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
goto v___jp_3497_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3469_);
v_a_3601_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3492_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3492_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3276_, 2);
goto v___jp_3475_;
}
}
v___jp_3475_:
{
lean_object* v_toCold_3476_; lean_object* v_cancelTk_x3f_3477_; 
v_toCold_3476_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3477_ = lean_ctor_get(v_toCold_3476_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3477_) == 1)
{
lean_object* v_val_3478_; uint8_t v___x_3479_; 
v_val_3478_ = lean_ctor_get(v_cancelTk_x3f_3477_, 0);
v___x_3479_ = l_IO_CancelToken_isSet(v_val_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
v___x_3480_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3469_, v___x_3474_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec_ref(v___x_3474_);
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3469_);
v___x_3481_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v___x_3490_; 
v___x_3490_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3469_, v___x_3474_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec_ref(v___x_3474_);
return v___x_3490_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3609_; 
v_cacheInferType_3609_ = lean_ctor_get_uint8(v_a_3277_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3609_ == 0)
{
goto v___jp_3282_;
}
else
{
uint8_t v___x_3610_; 
v___x_3610_ = l_Lean_Expr_hasMVar(v_e_3276_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_inc_ref(v_e_3276_);
v___x_3611_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3719_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3719_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3719_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3672_; lean_object* v_cache_3673_; lean_object* v_inferType_3674_; lean_object* v___x_3675_; 
v___x_3672_ = lean_st_ref_get(v_a_3278_);
v_cache_3673_ = lean_ctor_get(v___x_3672_, 1);
lean_inc_ref(v_cache_3673_);
lean_dec(v___x_3672_);
v_inferType_3674_ = lean_ctor_get(v_cache_3673_, 0);
lean_inc_ref(v_inferType_3674_);
lean_dec_ref(v_cache_3673_);
v___x_3675_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3674_, v_a_3612_);
if (lean_obj_tag(v___x_3675_) == 1)
{
lean_object* v_val_3676_; lean_object* v_fst_3677_; lean_object* v_snd_3678_; lean_object* v_expr_3679_; uint64_t v_configKey_3680_; lean_object* v_expr_3681_; uint64_t v_configKey_3682_; uint8_t v___x_3683_; 
v_val_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_val_3676_);
lean_dec_ref_known(v___x_3675_, 1);
v_fst_3677_ = lean_ctor_get(v_val_3676_, 0);
lean_inc(v_fst_3677_);
v_snd_3678_ = lean_ctor_get(v_val_3676_, 1);
lean_inc(v_snd_3678_);
lean_dec(v_val_3676_);
v_expr_3679_ = lean_ctor_get(v_a_3612_, 0);
v_configKey_3680_ = lean_ctor_get_uint64(v_a_3612_, sizeof(void*)*1);
v_expr_3681_ = lean_ctor_get(v_fst_3677_, 0);
lean_inc_ref(v_expr_3681_);
v_configKey_3682_ = lean_ctor_get_uint64(v_fst_3677_, sizeof(void*)*1);
lean_dec(v_fst_3677_);
v___x_3683_ = lean_uint64_dec_eq(v_configKey_3680_, v_configKey_3682_);
if (v___x_3683_ == 0)
{
lean_dec_ref(v_expr_3681_);
lean_dec(v_snd_3678_);
lean_dec_ref(v_inferType_3674_);
lean_del_object(v___x_3614_);
goto v___jp_3658_;
}
else
{
size_t v___x_3684_; uint8_t v___x_3685_; 
v___x_3684_ = ((size_t)64ULL);
v___x_3685_ = lean_expr_equal_budgeted(v_expr_3679_, v_expr_3681_, v___x_3684_);
lean_dec_ref(v_expr_3681_);
switch(v___x_3685_)
{
case 0:
{
lean_dec(v_snd_3678_);
lean_dec_ref(v_inferType_3674_);
lean_del_object(v___x_3614_);
goto v___jp_3658_;
}
case 1:
{
lean_object* v___x_3687_; 
lean_dec_ref(v_inferType_3674_);
lean_dec(v_a_3612_);
lean_dec_ref_known(v_e_3276_, 3);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v_snd_3678_);
v___x_3687_ = v___x_3614_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_snd_3678_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
default: 
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v_cache_3691_; lean_object* v_mctx_3692_; lean_object* v_zetaDeltaFVarIds_3693_; lean_object* v_postponed_3694_; lean_object* v_diag_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_snd_3678_);
lean_del_object(v___x_3614_);
v___x_3689_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3674_, v_a_3612_);
v___x_3690_ = lean_st_ref_take(v_a_3278_);
v_cache_3691_ = lean_ctor_get(v___x_3690_, 1);
v_mctx_3692_ = lean_ctor_get(v___x_3690_, 0);
v_zetaDeltaFVarIds_3693_ = lean_ctor_get(v___x_3690_, 2);
v_postponed_3694_ = lean_ctor_get(v___x_3690_, 3);
v_diag_3695_ = lean_ctor_get(v___x_3690_, 4);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3697_ = v___x_3690_;
v_isShared_3698_ = v_isSharedCheck_3718_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_diag_3695_);
lean_inc(v_postponed_3694_);
lean_inc(v_zetaDeltaFVarIds_3693_);
lean_inc(v_cache_3691_);
lean_inc(v_mctx_3692_);
lean_dec(v___x_3690_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3718_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_funInfo_3699_; lean_object* v_synthInstance_3700_; lean_object* v_whnf_3701_; lean_object* v_defEqTrans_3702_; lean_object* v_defEqPerm_3703_; lean_object* v_isUnitLike_3704_; lean_object* v_unfold_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3716_; 
v_funInfo_3699_ = lean_ctor_get(v_cache_3691_, 1);
v_synthInstance_3700_ = lean_ctor_get(v_cache_3691_, 2);
v_whnf_3701_ = lean_ctor_get(v_cache_3691_, 3);
v_defEqTrans_3702_ = lean_ctor_get(v_cache_3691_, 4);
v_defEqPerm_3703_ = lean_ctor_get(v_cache_3691_, 5);
v_isUnitLike_3704_ = lean_ctor_get(v_cache_3691_, 6);
v_unfold_3705_ = lean_ctor_get(v_cache_3691_, 7);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_cache_3691_);
if (v_isSharedCheck_3716_ == 0)
{
lean_object* v_unused_3717_; 
v_unused_3717_ = lean_ctor_get(v_cache_3691_, 0);
lean_dec(v_unused_3717_);
v___x_3707_ = v_cache_3691_;
v_isShared_3708_ = v_isSharedCheck_3716_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_unfold_3705_);
lean_inc(v_isUnitLike_3704_);
lean_inc(v_defEqPerm_3703_);
lean_inc(v_defEqTrans_3702_);
lean_inc(v_whnf_3701_);
lean_inc(v_synthInstance_3700_);
lean_inc(v_funInfo_3699_);
lean_dec(v_cache_3691_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3716_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 0, v___x_3689_);
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_funInfo_3699_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_synthInstance_3700_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_whnf_3701_);
lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_defEqTrans_3702_);
lean_ctor_set(v_reuseFailAlloc_3715_, 5, v_defEqPerm_3703_);
lean_ctor_set(v_reuseFailAlloc_3715_, 6, v_isUnitLike_3704_);
lean_ctor_set(v_reuseFailAlloc_3715_, 7, v_unfold_3705_);
v___x_3710_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 1, v___x_3710_);
v___x_3712_ = v___x_3697_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_mctx_3692_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_zetaDeltaFVarIds_3693_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_postponed_3694_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v_diag_3695_);
v___x_3712_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_st_ref_put(v_a_3278_, v___x_3712_);
goto v___jp_3658_;
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
lean_dec(v___x_3675_);
lean_dec_ref(v_inferType_3674_);
lean_del_object(v___x_3614_);
goto v___jp_3658_;
}
v___jp_3616_:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; uint8_t v___x_3619_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v___x_3619_ = l_Lean_Expr_hasMVar(v_a_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3656_; 
lean_inc(v_a_3618_);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v___x_3617_, 0);
lean_dec(v_unused_3657_);
v___x_3621_ = v___x_3617_;
v_isShared_3622_ = v_isSharedCheck_3656_;
goto v_resetjp_3620_;
}
else
{
lean_dec(v___x_3617_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3656_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v_cache_3624_; lean_object* v_mctx_3625_; lean_object* v_zetaDeltaFVarIds_3626_; lean_object* v_postponed_3627_; lean_object* v_diag_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3655_; 
v___x_3623_ = lean_st_ref_take(v_a_3278_);
v_cache_3624_ = lean_ctor_get(v___x_3623_, 1);
v_mctx_3625_ = lean_ctor_get(v___x_3623_, 0);
v_zetaDeltaFVarIds_3626_ = lean_ctor_get(v___x_3623_, 2);
v_postponed_3627_ = lean_ctor_get(v___x_3623_, 3);
v_diag_3628_ = lean_ctor_get(v___x_3623_, 4);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3630_ = v___x_3623_;
v_isShared_3631_ = v_isSharedCheck_3655_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_diag_3628_);
lean_inc(v_postponed_3627_);
lean_inc(v_zetaDeltaFVarIds_3626_);
lean_inc(v_cache_3624_);
lean_inc(v_mctx_3625_);
lean_dec(v___x_3623_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3655_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_inferType_3632_; lean_object* v_funInfo_3633_; lean_object* v_synthInstance_3634_; lean_object* v_whnf_3635_; lean_object* v_defEqTrans_3636_; lean_object* v_defEqPerm_3637_; lean_object* v_isUnitLike_3638_; lean_object* v_unfold_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3654_; 
v_inferType_3632_ = lean_ctor_get(v_cache_3624_, 0);
v_funInfo_3633_ = lean_ctor_get(v_cache_3624_, 1);
v_synthInstance_3634_ = lean_ctor_get(v_cache_3624_, 2);
v_whnf_3635_ = lean_ctor_get(v_cache_3624_, 3);
v_defEqTrans_3636_ = lean_ctor_get(v_cache_3624_, 4);
v_defEqPerm_3637_ = lean_ctor_get(v_cache_3624_, 5);
v_isUnitLike_3638_ = lean_ctor_get(v_cache_3624_, 6);
v_unfold_3639_ = lean_ctor_get(v_cache_3624_, 7);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_cache_3624_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3641_ = v_cache_3624_;
v_isShared_3642_ = v_isSharedCheck_3654_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_unfold_3639_);
lean_inc(v_isUnitLike_3638_);
lean_inc(v_defEqPerm_3637_);
lean_inc(v_defEqTrans_3636_);
lean_inc(v_whnf_3635_);
lean_inc(v_synthInstance_3634_);
lean_inc(v_funInfo_3633_);
lean_inc(v_inferType_3632_);
lean_dec(v_cache_3624_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3654_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_inc(v_a_3618_);
v___x_3643_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3632_, v_a_3612_, v_a_3618_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3643_);
v___x_3645_ = v___x_3641_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_funInfo_3633_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_synthInstance_3634_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_whnf_3635_);
lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_defEqTrans_3636_);
lean_ctor_set(v_reuseFailAlloc_3653_, 5, v_defEqPerm_3637_);
lean_ctor_set(v_reuseFailAlloc_3653_, 6, v_isUnitLike_3638_);
lean_ctor_set(v_reuseFailAlloc_3653_, 7, v_unfold_3639_);
v___x_3645_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v___x_3645_);
v___x_3647_ = v___x_3630_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_mctx_3625_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_zetaDeltaFVarIds_3626_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_postponed_3627_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v_diag_3628_);
v___x_3647_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3648_ = lean_st_ref_put(v_a_3278_, v___x_3647_);
if (v_isShared_3622_ == 0)
{
v___x_3650_ = v___x_3621_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3618_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3612_);
return v___x_3617_;
}
}
else
{
lean_dec(v_a_3612_);
return v___x_3617_;
}
}
v___jp_3658_:
{
lean_object* v_toCold_3659_; lean_object* v_cancelTk_x3f_3660_; 
v_toCold_3659_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3660_ = lean_ctor_get(v_toCold_3659_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3660_) == 1)
{
lean_object* v_val_3661_; uint8_t v___x_3662_; 
v_val_3661_ = lean_ctor_get(v_cancelTk_x3f_3660_, 0);
v___x_3662_ = l_IO_CancelToken_isSet(v_val_3661_);
if (v___x_3662_ == 0)
{
goto v___jp_3616_;
}
else
{
lean_object* v___x_3663_; lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3612_);
lean_dec_ref_known(v_e_3276_, 3);
v___x_3663_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
goto v___jp_3616_;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref_known(v_e_3276_, 3);
v_a_3720_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3611_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3611_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
goto v___jp_3282_;
}
}
}
case 9:
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3728_ = lean_ctor_get(v_e_3276_, 0);
lean_inc_ref(v_a_3728_);
lean_dec_ref_known(v_e_3276_, 1);
v___x_3729_ = l_Lean_Literal_type(v_a_3728_);
lean_dec_ref(v_a_3728_);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
case 10:
{
lean_object* v_expr_3731_; 
v_expr_3731_ = lean_ctor_get(v_e_3276_, 1);
lean_inc_ref(v_expr_3731_);
lean_dec_ref_known(v_e_3276_, 2);
v_e_3276_ = v_expr_3731_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3733_; lean_object* v_idx_3734_; lean_object* v_struct_3735_; uint8_t v_cacheInferType_3752_; 
v_typeName_3733_ = lean_ctor_get(v_e_3276_, 0);
lean_inc(v_typeName_3733_);
v_idx_3734_ = lean_ctor_get(v_e_3276_, 1);
lean_inc(v_idx_3734_);
v_struct_3735_ = lean_ctor_get(v_e_3276_, 2);
lean_inc_ref(v_struct_3735_);
v_cacheInferType_3752_ = lean_ctor_get_uint8(v_a_3277_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3752_ == 0)
{
lean_dec_ref_known(v_e_3276_, 3);
goto v___jp_3736_;
}
else
{
uint8_t v___x_3753_; 
v___x_3753_ = l_Lean_Expr_hasMVar(v_e_3276_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3862_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3862_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3862_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3815_; lean_object* v_cache_3816_; lean_object* v_inferType_3817_; lean_object* v___x_3818_; 
v___x_3815_ = lean_st_ref_get(v_a_3278_);
v_cache_3816_ = lean_ctor_get(v___x_3815_, 1);
lean_inc_ref(v_cache_3816_);
lean_dec(v___x_3815_);
v_inferType_3817_ = lean_ctor_get(v_cache_3816_, 0);
lean_inc_ref(v_inferType_3817_);
lean_dec_ref(v_cache_3816_);
v___x_3818_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3817_, v_a_3755_);
if (lean_obj_tag(v___x_3818_) == 1)
{
lean_object* v_val_3819_; lean_object* v_fst_3820_; lean_object* v_snd_3821_; lean_object* v_expr_3822_; uint64_t v_configKey_3823_; lean_object* v_expr_3824_; uint64_t v_configKey_3825_; uint8_t v___x_3826_; 
v_val_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_val_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v_fst_3820_ = lean_ctor_get(v_val_3819_, 0);
lean_inc(v_fst_3820_);
v_snd_3821_ = lean_ctor_get(v_val_3819_, 1);
lean_inc(v_snd_3821_);
lean_dec(v_val_3819_);
v_expr_3822_ = lean_ctor_get(v_a_3755_, 0);
v_configKey_3823_ = lean_ctor_get_uint64(v_a_3755_, sizeof(void*)*1);
v_expr_3824_ = lean_ctor_get(v_fst_3820_, 0);
lean_inc_ref(v_expr_3824_);
v_configKey_3825_ = lean_ctor_get_uint64(v_fst_3820_, sizeof(void*)*1);
lean_dec(v_fst_3820_);
v___x_3826_ = lean_uint64_dec_eq(v_configKey_3823_, v_configKey_3825_);
if (v___x_3826_ == 0)
{
lean_dec_ref(v_expr_3824_);
lean_dec(v_snd_3821_);
lean_dec_ref(v_inferType_3817_);
lean_del_object(v___x_3757_);
goto v___jp_3801_;
}
else
{
size_t v___x_3827_; uint8_t v___x_3828_; 
v___x_3827_ = ((size_t)64ULL);
v___x_3828_ = lean_expr_equal_budgeted(v_expr_3822_, v_expr_3824_, v___x_3827_);
lean_dec_ref(v_expr_3824_);
switch(v___x_3828_)
{
case 0:
{
lean_dec(v_snd_3821_);
lean_dec_ref(v_inferType_3817_);
lean_del_object(v___x_3757_);
goto v___jp_3801_;
}
case 1:
{
lean_object* v___x_3830_; 
lean_dec_ref(v_inferType_3817_);
lean_dec(v_a_3755_);
lean_dec_ref(v_struct_3735_);
lean_dec(v_idx_3734_);
lean_dec(v_typeName_3733_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v_snd_3821_);
v___x_3830_ = v___x_3757_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_snd_3821_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
default: 
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_cache_3834_; lean_object* v_mctx_3835_; lean_object* v_zetaDeltaFVarIds_3836_; lean_object* v_postponed_3837_; lean_object* v_diag_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_snd_3821_);
lean_del_object(v___x_3757_);
v___x_3832_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3817_, v_a_3755_);
v___x_3833_ = lean_st_ref_take(v_a_3278_);
v_cache_3834_ = lean_ctor_get(v___x_3833_, 1);
v_mctx_3835_ = lean_ctor_get(v___x_3833_, 0);
v_zetaDeltaFVarIds_3836_ = lean_ctor_get(v___x_3833_, 2);
v_postponed_3837_ = lean_ctor_get(v___x_3833_, 3);
v_diag_3838_ = lean_ctor_get(v___x_3833_, 4);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3840_ = v___x_3833_;
v_isShared_3841_ = v_isSharedCheck_3861_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_diag_3838_);
lean_inc(v_postponed_3837_);
lean_inc(v_zetaDeltaFVarIds_3836_);
lean_inc(v_cache_3834_);
lean_inc(v_mctx_3835_);
lean_dec(v___x_3833_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3861_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_funInfo_3842_; lean_object* v_synthInstance_3843_; lean_object* v_whnf_3844_; lean_object* v_defEqTrans_3845_; lean_object* v_defEqPerm_3846_; lean_object* v_isUnitLike_3847_; lean_object* v_unfold_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3859_; 
v_funInfo_3842_ = lean_ctor_get(v_cache_3834_, 1);
v_synthInstance_3843_ = lean_ctor_get(v_cache_3834_, 2);
v_whnf_3844_ = lean_ctor_get(v_cache_3834_, 3);
v_defEqTrans_3845_ = lean_ctor_get(v_cache_3834_, 4);
v_defEqPerm_3846_ = lean_ctor_get(v_cache_3834_, 5);
v_isUnitLike_3847_ = lean_ctor_get(v_cache_3834_, 6);
v_unfold_3848_ = lean_ctor_get(v_cache_3834_, 7);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_cache_3834_);
if (v_isSharedCheck_3859_ == 0)
{
lean_object* v_unused_3860_; 
v_unused_3860_ = lean_ctor_get(v_cache_3834_, 0);
lean_dec(v_unused_3860_);
v___x_3850_ = v_cache_3834_;
v_isShared_3851_ = v_isSharedCheck_3859_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_unfold_3848_);
lean_inc(v_isUnitLike_3847_);
lean_inc(v_defEqPerm_3846_);
lean_inc(v_defEqTrans_3845_);
lean_inc(v_whnf_3844_);
lean_inc(v_synthInstance_3843_);
lean_inc(v_funInfo_3842_);
lean_dec(v_cache_3834_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3859_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v___x_3832_);
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_funInfo_3842_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_synthInstance_3843_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_whnf_3844_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_defEqTrans_3845_);
lean_ctor_set(v_reuseFailAlloc_3858_, 5, v_defEqPerm_3846_);
lean_ctor_set(v_reuseFailAlloc_3858_, 6, v_isUnitLike_3847_);
lean_ctor_set(v_reuseFailAlloc_3858_, 7, v_unfold_3848_);
v___x_3853_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 1, v___x_3853_);
v___x_3855_ = v___x_3840_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_mctx_3835_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_zetaDeltaFVarIds_3836_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v_postponed_3837_);
lean_ctor_set(v_reuseFailAlloc_3857_, 4, v_diag_3838_);
v___x_3855_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_st_ref_put(v_a_3278_, v___x_3855_);
goto v___jp_3801_;
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
lean_dec(v___x_3818_);
lean_dec_ref(v_inferType_3817_);
lean_del_object(v___x_3757_);
goto v___jp_3801_;
}
v___jp_3759_:
{
lean_object* v___x_3760_; 
v___x_3760_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3733_, v_idx_3734_, v_struct_3735_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; uint8_t v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v___x_3762_ = l_Lean_Expr_hasMVar(v_a_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3799_; 
lean_inc(v_a_3761_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3800_);
v___x_3764_ = v___x_3760_;
v_isShared_3765_ = v_isSharedCheck_3799_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3760_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3799_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v_cache_3767_; lean_object* v_mctx_3768_; lean_object* v_zetaDeltaFVarIds_3769_; lean_object* v_postponed_3770_; lean_object* v_diag_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3798_; 
v___x_3766_ = lean_st_ref_take(v_a_3278_);
v_cache_3767_ = lean_ctor_get(v___x_3766_, 1);
v_mctx_3768_ = lean_ctor_get(v___x_3766_, 0);
v_zetaDeltaFVarIds_3769_ = lean_ctor_get(v___x_3766_, 2);
v_postponed_3770_ = lean_ctor_get(v___x_3766_, 3);
v_diag_3771_ = lean_ctor_get(v___x_3766_, 4);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3773_ = v___x_3766_;
v_isShared_3774_ = v_isSharedCheck_3798_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_diag_3771_);
lean_inc(v_postponed_3770_);
lean_inc(v_zetaDeltaFVarIds_3769_);
lean_inc(v_cache_3767_);
lean_inc(v_mctx_3768_);
lean_dec(v___x_3766_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3798_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v_inferType_3775_; lean_object* v_funInfo_3776_; lean_object* v_synthInstance_3777_; lean_object* v_whnf_3778_; lean_object* v_defEqTrans_3779_; lean_object* v_defEqPerm_3780_; lean_object* v_isUnitLike_3781_; lean_object* v_unfold_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3797_; 
v_inferType_3775_ = lean_ctor_get(v_cache_3767_, 0);
v_funInfo_3776_ = lean_ctor_get(v_cache_3767_, 1);
v_synthInstance_3777_ = lean_ctor_get(v_cache_3767_, 2);
v_whnf_3778_ = lean_ctor_get(v_cache_3767_, 3);
v_defEqTrans_3779_ = lean_ctor_get(v_cache_3767_, 4);
v_defEqPerm_3780_ = lean_ctor_get(v_cache_3767_, 5);
v_isUnitLike_3781_ = lean_ctor_get(v_cache_3767_, 6);
v_unfold_3782_ = lean_ctor_get(v_cache_3767_, 7);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_cache_3767_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3784_ = v_cache_3767_;
v_isShared_3785_ = v_isSharedCheck_3797_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_unfold_3782_);
lean_inc(v_isUnitLike_3781_);
lean_inc(v_defEqPerm_3780_);
lean_inc(v_defEqTrans_3779_);
lean_inc(v_whnf_3778_);
lean_inc(v_synthInstance_3777_);
lean_inc(v_funInfo_3776_);
lean_inc(v_inferType_3775_);
lean_dec(v_cache_3767_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3797_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v___x_3788_; 
lean_inc(v_a_3761_);
v___x_3786_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3775_, v_a_3755_, v_a_3761_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3786_);
v___x_3788_ = v___x_3784_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_funInfo_3776_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_synthInstance_3777_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_whnf_3778_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_defEqTrans_3779_);
lean_ctor_set(v_reuseFailAlloc_3796_, 5, v_defEqPerm_3780_);
lean_ctor_set(v_reuseFailAlloc_3796_, 6, v_isUnitLike_3781_);
lean_ctor_set(v_reuseFailAlloc_3796_, 7, v_unfold_3782_);
v___x_3788_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3790_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v___x_3788_);
v___x_3790_ = v___x_3773_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_mctx_3768_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_zetaDeltaFVarIds_3769_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_postponed_3770_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_diag_3771_);
v___x_3790_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3791_ = lean_st_ref_put(v_a_3278_, v___x_3790_);
if (v_isShared_3765_ == 0)
{
v___x_3793_ = v___x_3764_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3761_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3755_);
return v___x_3760_;
}
}
else
{
lean_dec(v_a_3755_);
return v___x_3760_;
}
}
v___jp_3801_:
{
lean_object* v_toCold_3802_; lean_object* v_cancelTk_x3f_3803_; 
v_toCold_3802_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3803_ = lean_ctor_get(v_toCold_3802_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3803_) == 1)
{
lean_object* v_val_3804_; uint8_t v___x_3805_; 
v_val_3804_ = lean_ctor_get(v_cancelTk_x3f_3803_, 0);
v___x_3805_ = l_IO_CancelToken_isSet(v_val_3804_);
if (v___x_3805_ == 0)
{
goto v___jp_3759_;
}
else
{
lean_object* v___x_3806_; lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec(v_a_3755_);
lean_dec_ref(v_struct_3735_);
lean_dec(v_idx_3734_);
lean_dec(v_typeName_3733_);
v___x_3806_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
goto v___jp_3759_;
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v_struct_3735_);
lean_dec(v_idx_3734_);
lean_dec(v_typeName_3733_);
v_a_3863_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3754_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3754_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3276_, 3);
goto v___jp_3736_;
}
}
v___jp_3736_:
{
lean_object* v_toCold_3737_; lean_object* v_cancelTk_x3f_3738_; 
v_toCold_3737_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3738_ = lean_ctor_get(v_toCold_3737_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3738_) == 1)
{
lean_object* v_val_3739_; uint8_t v___x_3740_; 
v_val_3739_ = lean_ctor_get(v_cancelTk_x3f_3738_, 0);
v___x_3740_ = l_IO_CancelToken_isSet(v_val_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3733_, v_idx_3734_, v_struct_3735_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_struct_3735_);
lean_dec(v_idx_3734_);
lean_dec(v_typeName_3733_);
v___x_3742_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3733_, v_idx_3734_, v_struct_3735_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3751_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3871_; 
v_cacheInferType_3871_ = lean_ctor_get_uint8(v_a_3277_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3871_ == 0)
{
goto v___jp_3298_;
}
else
{
uint8_t v___x_3872_; 
v___x_3872_ = l_Lean_Expr_hasMVar(v_e_3276_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; 
lean_inc_ref(v_e_3276_);
v___x_3873_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3276_, v_a_3277_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3981_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3981_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3981_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3934_; lean_object* v_cache_3935_; lean_object* v_inferType_3936_; lean_object* v___x_3937_; 
v___x_3934_ = lean_st_ref_get(v_a_3278_);
v_cache_3935_ = lean_ctor_get(v___x_3934_, 1);
lean_inc_ref(v_cache_3935_);
lean_dec(v___x_3934_);
v_inferType_3936_ = lean_ctor_get(v_cache_3935_, 0);
lean_inc_ref(v_inferType_3936_);
lean_dec_ref(v_cache_3935_);
v___x_3937_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3936_, v_a_3874_);
if (lean_obj_tag(v___x_3937_) == 1)
{
lean_object* v_val_3938_; lean_object* v_fst_3939_; lean_object* v_snd_3940_; lean_object* v_expr_3941_; uint64_t v_configKey_3942_; lean_object* v_expr_3943_; uint64_t v_configKey_3944_; uint8_t v___x_3945_; 
v_val_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v_fst_3939_ = lean_ctor_get(v_val_3938_, 0);
lean_inc(v_fst_3939_);
v_snd_3940_ = lean_ctor_get(v_val_3938_, 1);
lean_inc(v_snd_3940_);
lean_dec(v_val_3938_);
v_expr_3941_ = lean_ctor_get(v_a_3874_, 0);
v_configKey_3942_ = lean_ctor_get_uint64(v_a_3874_, sizeof(void*)*1);
v_expr_3943_ = lean_ctor_get(v_fst_3939_, 0);
lean_inc_ref(v_expr_3943_);
v_configKey_3944_ = lean_ctor_get_uint64(v_fst_3939_, sizeof(void*)*1);
lean_dec(v_fst_3939_);
v___x_3945_ = lean_uint64_dec_eq(v_configKey_3942_, v_configKey_3944_);
if (v___x_3945_ == 0)
{
lean_dec_ref(v_expr_3943_);
lean_dec(v_snd_3940_);
lean_dec_ref(v_inferType_3936_);
lean_del_object(v___x_3876_);
goto v___jp_3920_;
}
else
{
size_t v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = ((size_t)64ULL);
v___x_3947_ = lean_expr_equal_budgeted(v_expr_3941_, v_expr_3943_, v___x_3946_);
lean_dec_ref(v_expr_3943_);
switch(v___x_3947_)
{
case 0:
{
lean_dec(v_snd_3940_);
lean_dec_ref(v_inferType_3936_);
lean_del_object(v___x_3876_);
goto v___jp_3920_;
}
case 1:
{
lean_object* v___x_3949_; 
lean_dec_ref(v_inferType_3936_);
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3276_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v_snd_3940_);
v___x_3949_ = v___x_3876_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_snd_3940_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
default: 
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v_cache_3953_; lean_object* v_mctx_3954_; lean_object* v_zetaDeltaFVarIds_3955_; lean_object* v_postponed_3956_; lean_object* v_diag_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_snd_3940_);
lean_del_object(v___x_3876_);
v___x_3951_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3936_, v_a_3874_);
v___x_3952_ = lean_st_ref_take(v_a_3278_);
v_cache_3953_ = lean_ctor_get(v___x_3952_, 1);
v_mctx_3954_ = lean_ctor_get(v___x_3952_, 0);
v_zetaDeltaFVarIds_3955_ = lean_ctor_get(v___x_3952_, 2);
v_postponed_3956_ = lean_ctor_get(v___x_3952_, 3);
v_diag_3957_ = lean_ctor_get(v___x_3952_, 4);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3959_ = v___x_3952_;
v_isShared_3960_ = v_isSharedCheck_3980_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_diag_3957_);
lean_inc(v_postponed_3956_);
lean_inc(v_zetaDeltaFVarIds_3955_);
lean_inc(v_cache_3953_);
lean_inc(v_mctx_3954_);
lean_dec(v___x_3952_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3980_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v_funInfo_3961_; lean_object* v_synthInstance_3962_; lean_object* v_whnf_3963_; lean_object* v_defEqTrans_3964_; lean_object* v_defEqPerm_3965_; lean_object* v_isUnitLike_3966_; lean_object* v_unfold_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3978_; 
v_funInfo_3961_ = lean_ctor_get(v_cache_3953_, 1);
v_synthInstance_3962_ = lean_ctor_get(v_cache_3953_, 2);
v_whnf_3963_ = lean_ctor_get(v_cache_3953_, 3);
v_defEqTrans_3964_ = lean_ctor_get(v_cache_3953_, 4);
v_defEqPerm_3965_ = lean_ctor_get(v_cache_3953_, 5);
v_isUnitLike_3966_ = lean_ctor_get(v_cache_3953_, 6);
v_unfold_3967_ = lean_ctor_get(v_cache_3953_, 7);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_cache_3953_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v_cache_3953_, 0);
lean_dec(v_unused_3979_);
v___x_3969_ = v_cache_3953_;
v_isShared_3970_ = v_isSharedCheck_3978_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_unfold_3967_);
lean_inc(v_isUnitLike_3966_);
lean_inc(v_defEqPerm_3965_);
lean_inc(v_defEqTrans_3964_);
lean_inc(v_whnf_3963_);
lean_inc(v_synthInstance_3962_);
lean_inc(v_funInfo_3961_);
lean_dec(v_cache_3953_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3978_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3951_);
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_funInfo_3961_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_synthInstance_3962_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_whnf_3963_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_defEqTrans_3964_);
lean_ctor_set(v_reuseFailAlloc_3977_, 5, v_defEqPerm_3965_);
lean_ctor_set(v_reuseFailAlloc_3977_, 6, v_isUnitLike_3966_);
lean_ctor_set(v_reuseFailAlloc_3977_, 7, v_unfold_3967_);
v___x_3972_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3974_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 1, v___x_3972_);
v___x_3974_ = v___x_3959_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_mctx_3954_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_zetaDeltaFVarIds_3955_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v_postponed_3956_);
lean_ctor_set(v_reuseFailAlloc_3976_, 4, v_diag_3957_);
v___x_3974_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_st_ref_put(v_a_3278_, v___x_3974_);
goto v___jp_3920_;
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
lean_dec(v___x_3937_);
lean_dec_ref(v_inferType_3936_);
lean_del_object(v___x_3876_);
goto v___jp_3920_;
}
v___jp_3878_:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; uint8_t v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v___x_3881_ = l_Lean_Expr_hasMVar(v_a_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3918_; 
lean_inc(v_a_3880_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v___x_3879_, 0);
lean_dec(v_unused_3919_);
v___x_3883_ = v___x_3879_;
v_isShared_3884_ = v_isSharedCheck_3918_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v___x_3879_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3918_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v_cache_3886_; lean_object* v_mctx_3887_; lean_object* v_zetaDeltaFVarIds_3888_; lean_object* v_postponed_3889_; lean_object* v_diag_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3917_; 
v___x_3885_ = lean_st_ref_take(v_a_3278_);
v_cache_3886_ = lean_ctor_get(v___x_3885_, 1);
v_mctx_3887_ = lean_ctor_get(v___x_3885_, 0);
v_zetaDeltaFVarIds_3888_ = lean_ctor_get(v___x_3885_, 2);
v_postponed_3889_ = lean_ctor_get(v___x_3885_, 3);
v_diag_3890_ = lean_ctor_get(v___x_3885_, 4);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3892_ = v___x_3885_;
v_isShared_3893_ = v_isSharedCheck_3917_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_diag_3890_);
lean_inc(v_postponed_3889_);
lean_inc(v_zetaDeltaFVarIds_3888_);
lean_inc(v_cache_3886_);
lean_inc(v_mctx_3887_);
lean_dec(v___x_3885_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3917_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v_inferType_3894_; lean_object* v_funInfo_3895_; lean_object* v_synthInstance_3896_; lean_object* v_whnf_3897_; lean_object* v_defEqTrans_3898_; lean_object* v_defEqPerm_3899_; lean_object* v_isUnitLike_3900_; lean_object* v_unfold_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3916_; 
v_inferType_3894_ = lean_ctor_get(v_cache_3886_, 0);
v_funInfo_3895_ = lean_ctor_get(v_cache_3886_, 1);
v_synthInstance_3896_ = lean_ctor_get(v_cache_3886_, 2);
v_whnf_3897_ = lean_ctor_get(v_cache_3886_, 3);
v_defEqTrans_3898_ = lean_ctor_get(v_cache_3886_, 4);
v_defEqPerm_3899_ = lean_ctor_get(v_cache_3886_, 5);
v_isUnitLike_3900_ = lean_ctor_get(v_cache_3886_, 6);
v_unfold_3901_ = lean_ctor_get(v_cache_3886_, 7);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_cache_3886_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3903_ = v_cache_3886_;
v_isShared_3904_ = v_isSharedCheck_3916_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_unfold_3901_);
lean_inc(v_isUnitLike_3900_);
lean_inc(v_defEqPerm_3899_);
lean_inc(v_defEqTrans_3898_);
lean_inc(v_whnf_3897_);
lean_inc(v_synthInstance_3896_);
lean_inc(v_funInfo_3895_);
lean_inc(v_inferType_3894_);
lean_dec(v_cache_3886_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3916_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_inc(v_a_3880_);
v___x_3905_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3894_, v_a_3874_, v_a_3880_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3905_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_funInfo_3895_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_synthInstance_3896_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v_whnf_3897_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v_defEqTrans_3898_);
lean_ctor_set(v_reuseFailAlloc_3915_, 5, v_defEqPerm_3899_);
lean_ctor_set(v_reuseFailAlloc_3915_, 6, v_isUnitLike_3900_);
lean_ctor_set(v_reuseFailAlloc_3915_, 7, v_unfold_3901_);
v___x_3907_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v___x_3907_);
v___x_3909_ = v___x_3892_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_mctx_3887_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3914_, 2, v_zetaDeltaFVarIds_3888_);
lean_ctor_set(v_reuseFailAlloc_3914_, 3, v_postponed_3889_);
lean_ctor_set(v_reuseFailAlloc_3914_, 4, v_diag_3890_);
v___x_3909_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_st_ref_put(v_a_3278_, v___x_3909_);
if (v_isShared_3884_ == 0)
{
v___x_3912_ = v___x_3883_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3880_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3874_);
return v___x_3879_;
}
}
else
{
lean_dec(v_a_3874_);
return v___x_3879_;
}
}
v___jp_3920_:
{
lean_object* v_toCold_3921_; lean_object* v_cancelTk_x3f_3922_; 
v_toCold_3921_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3922_ = lean_ctor_get(v_toCold_3921_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3922_) == 1)
{
lean_object* v_val_3923_; uint8_t v___x_3924_; 
v_val_3923_ = lean_ctor_get(v_cancelTk_x3f_3922_, 0);
v___x_3924_ = l_IO_CancelToken_isSet(v_val_3923_);
if (v___x_3924_ == 0)
{
goto v___jp_3878_;
}
else
{
lean_object* v___x_3925_; lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3874_);
lean_dec_ref(v_e_3276_);
v___x_3925_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
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
else
{
goto v___jp_3878_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_e_3276_);
v_a_3982_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3873_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3873_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
else
{
goto v___jp_3298_;
}
}
}
}
v___jp_3282_:
{
lean_object* v_toCold_3283_; lean_object* v_cancelTk_x3f_3284_; 
v_toCold_3283_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3284_ = lean_ctor_get(v_toCold_3283_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3284_) == 1)
{
lean_object* v_val_3285_; uint8_t v___x_3286_; 
v_val_3285_ = lean_ctor_get(v_cancelTk_x3f_3284_, 0);
v___x_3286_ = l_IO_CancelToken_isSet(v_val_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_e_3276_);
v___x_3288_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3297_;
}
}
v___jp_3298_:
{
lean_object* v_toCold_3299_; lean_object* v_cancelTk_x3f_3300_; 
v_toCold_3299_ = lean_ctor_get(v_a_3279_, 0);
v_cancelTk_x3f_3300_ = lean_ctor_get(v_toCold_3299_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3300_) == 1)
{
lean_object* v_val_3301_; uint8_t v___x_3302_; 
v_val_3301_ = lean_ctor_get(v_cancelTk_x3f_3300_, 0);
v___x_3302_ = l_IO_CancelToken_isSet(v_val_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref(v_e_3276_);
v___x_3304_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v___x_3313_; 
v___x_3313_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3997_, lean_object* v_x_3998_, lean_object* v_x_3999_, lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3998_, v_x_3999_, v_x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_4002_, lean_object* v_x_4003_, lean_object* v_x_4004_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_4003_, v_x_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_4006_, lean_object* v_x_4007_, lean_object* v_x_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_4006_, v_x_4007_, v_x_4008_);
lean_dec_ref(v_x_4008_);
lean_dec_ref(v_x_4007_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(lean_object* v_00_u03b2_4010_, lean_object* v_x_4011_, lean_object* v_x_4012_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_4011_, v_x_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___boxed(lean_object* v_00_u03b2_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(v_00_u03b2_4014_, v_x_4015_, v_x_4016_);
lean_dec_ref(v_x_4016_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_4018_, lean_object* v_x_4019_, size_t v_x_4020_, size_t v_x_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_4019_, v_x_4020_, v_x_4021_, v_x_4022_, v_x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v_x_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
size_t v_x_5650__boxed_4031_; size_t v_x_5651__boxed_4032_; lean_object* v_res_4033_; 
v_x_5650__boxed_4031_ = lean_unbox_usize(v_x_4027_);
lean_dec(v_x_4027_);
v_x_5651__boxed_4032_ = lean_unbox_usize(v_x_4028_);
lean_dec(v_x_4028_);
v_res_4033_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_4025_, v_x_4026_, v_x_5650__boxed_4031_, v_x_5651__boxed_4032_, v_x_4029_, v_x_4030_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_4034_, lean_object* v_x_4035_, size_t v_x_4036_, lean_object* v_x_4037_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_4035_, v_x_4036_, v_x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4039_, lean_object* v_x_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_){
_start:
{
size_t v_x_5667__boxed_4043_; lean_object* v_res_4044_; 
v_x_5667__boxed_4043_ = lean_unbox_usize(v_x_4041_);
lean_dec(v_x_4041_);
v_res_4044_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_4039_, v_x_4040_, v_x_5667__boxed_4043_, v_x_4042_);
lean_dec_ref(v_x_4042_);
lean_dec_ref(v_x_4040_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(lean_object* v_00_u03b2_4045_, lean_object* v_x_4046_, size_t v_x_4047_, lean_object* v_x_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_4046_, v_x_4047_, v_x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4050_, lean_object* v_x_4051_, lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
size_t v_x_5678__boxed_4054_; lean_object* v_res_4055_; 
v_x_5678__boxed_4054_ = lean_unbox_usize(v_x_4052_);
lean_dec(v_x_4052_);
v_res_4055_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(v_00_u03b2_4050_, v_x_4051_, v_x_5678__boxed_4054_, v_x_4053_);
lean_dec_ref(v_x_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4056_, lean_object* v_n_4057_, lean_object* v_k_4058_, lean_object* v_v_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_4057_, v_k_4058_, v_v_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_4061_, size_t v_depth_4062_, lean_object* v_keys_4063_, lean_object* v_vals_4064_, lean_object* v_heq_4065_, lean_object* v_i_4066_, lean_object* v_entries_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_4062_, v_keys_4063_, v_vals_4064_, v_i_4066_, v_entries_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4069_, lean_object* v_depth_4070_, lean_object* v_keys_4071_, lean_object* v_vals_4072_, lean_object* v_heq_4073_, lean_object* v_i_4074_, lean_object* v_entries_4075_){
_start:
{
size_t v_depth_boxed_4076_; lean_object* v_res_4077_; 
v_depth_boxed_4076_ = lean_unbox_usize(v_depth_4070_);
lean_dec(v_depth_4070_);
v_res_4077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_4069_, v_depth_boxed_4076_, v_keys_4071_, v_vals_4072_, v_heq_4073_, v_i_4074_, v_entries_4075_);
lean_dec_ref(v_vals_4072_);
lean_dec_ref(v_keys_4071_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4078_, lean_object* v_keys_4079_, lean_object* v_vals_4080_, lean_object* v_heq_4081_, lean_object* v_i_4082_, lean_object* v_k_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_4079_, v_vals_4080_, v_i_4082_, v_k_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4085_, lean_object* v_keys_4086_, lean_object* v_vals_4087_, lean_object* v_heq_4088_, lean_object* v_i_4089_, lean_object* v_k_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_4085_, v_keys_4086_, v_vals_4087_, v_heq_4088_, v_i_4089_, v_k_4090_);
lean_dec_ref(v_k_4090_);
lean_dec_ref(v_vals_4087_);
lean_dec_ref(v_keys_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4092_, lean_object* v_x_4093_, lean_object* v_x_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_x_4093_, v_x_4094_, v_x_4095_, v_x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = l_Lean_maxRecDepthErrorMessage;
v___x_4104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_4106_ = l_Lean_MessageData_ofFormat(v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_4108_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_4109_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v___x_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_4110_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4113_, 0, v_ref_4110_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4115_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_4118_, lean_object* v_ref_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4119_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_4126_, lean_object* v_ref_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_4126_, v_ref_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4186_; uint8_t v_beta_4187_; 
v___x_4186_ = l_Lean_Meta_Context_config(v___y_4135_);
v_beta_4187_ = lean_ctor_get_uint8(v___x_4186_, 13);
if (v_beta_4187_ == 0)
{
lean_dec_ref(v___x_4186_);
goto v___jp_4140_;
}
else
{
uint8_t v_iota_4188_; 
v_iota_4188_ = lean_ctor_get_uint8(v___x_4186_, 12);
if (v_iota_4188_ == 0)
{
lean_dec_ref(v___x_4186_);
goto v___jp_4140_;
}
else
{
uint8_t v_zeta_4189_; 
v_zeta_4189_ = lean_ctor_get_uint8(v___x_4186_, 15);
if (v_zeta_4189_ == 0)
{
lean_dec_ref(v___x_4186_);
goto v___jp_4140_;
}
else
{
uint8_t v_zetaHave_4190_; 
v_zetaHave_4190_ = lean_ctor_get_uint8(v___x_4186_, 18);
if (v_zetaHave_4190_ == 0)
{
lean_dec_ref(v___x_4186_);
goto v___jp_4140_;
}
else
{
uint8_t v_zetaDelta_4191_; 
v_zetaDelta_4191_ = lean_ctor_get_uint8(v___x_4186_, 16);
if (v_zetaDelta_4191_ == 0)
{
lean_dec_ref(v___x_4186_);
goto v___jp_4140_;
}
else
{
uint8_t v_etaStruct_4192_; uint8_t v_proj_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v_etaStruct_4192_ = lean_ctor_get_uint8(v___x_4186_, 10);
v_proj_4193_ = lean_ctor_get_uint8(v___x_4186_, 14);
lean_dec_ref(v___x_4186_);
v___x_4194_ = lean_box(v_proj_4193_);
v___x_4195_ = lean_obj_tag_nat(v___x_4194_);
lean_dec(v___x_4194_);
v___x_4196_ = lean_unsigned_to_nat(2u);
v___x_4197_ = lean_nat_dec_eq(v___x_4195_, v___x_4196_);
if (v___x_4197_ == 0)
{
goto v___jp_4140_;
}
else
{
uint8_t v___x_4198_; uint8_t v___x_4199_; 
v___x_4198_ = 0;
v___x_4199_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4192_, v___x_4198_);
if (v___x_4199_ == 0)
{
goto v___jp_4140_;
}
else
{
lean_object* v___x_4200_; 
v___x_4200_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec_ref(v___y_4135_);
return v___x_4200_;
}
}
}
}
}
}
}
v___jp_4140_:
{
lean_object* v___x_4141_; uint8_t v_foApprox_4142_; uint8_t v_ctxApprox_4143_; uint8_t v_quasiPatternApprox_4144_; uint8_t v_constApprox_4145_; uint8_t v_isDefEqStuckEx_4146_; uint8_t v_unificationHints_4147_; uint8_t v_proofIrrelevance_4148_; uint8_t v_assignSyntheticOpaque_4149_; uint8_t v_offsetCnstrs_4150_; uint8_t v_transparency_4151_; uint8_t v_univApprox_4152_; uint8_t v_zetaUnused_4153_; uint8_t v_canUnfoldPredicateConfig_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4185_; 
v___x_4141_ = l_Lean_Meta_Context_config(v___y_4135_);
v_foApprox_4142_ = lean_ctor_get_uint8(v___x_4141_, 0);
v_ctxApprox_4143_ = lean_ctor_get_uint8(v___x_4141_, 1);
v_quasiPatternApprox_4144_ = lean_ctor_get_uint8(v___x_4141_, 2);
v_constApprox_4145_ = lean_ctor_get_uint8(v___x_4141_, 3);
v_isDefEqStuckEx_4146_ = lean_ctor_get_uint8(v___x_4141_, 4);
v_unificationHints_4147_ = lean_ctor_get_uint8(v___x_4141_, 5);
v_proofIrrelevance_4148_ = lean_ctor_get_uint8(v___x_4141_, 6);
v_assignSyntheticOpaque_4149_ = lean_ctor_get_uint8(v___x_4141_, 7);
v_offsetCnstrs_4150_ = lean_ctor_get_uint8(v___x_4141_, 8);
v_transparency_4151_ = lean_ctor_get_uint8(v___x_4141_, 9);
v_univApprox_4152_ = lean_ctor_get_uint8(v___x_4141_, 11);
v_zetaUnused_4153_ = lean_ctor_get_uint8(v___x_4141_, 17);
v_canUnfoldPredicateConfig_4154_ = lean_ctor_get_uint8(v___x_4141_, 19);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4156_ = v___x_4141_;
v_isShared_4157_ = v_isSharedCheck_4185_;
goto v_resetjp_4155_;
}
else
{
lean_dec(v___x_4141_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4185_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
uint8_t v___x_4158_; uint8_t v___x_4159_; uint8_t v___x_4160_; lean_object* v___x_4162_; 
v___x_4158_ = 1;
v___x_4159_ = 0;
v___x_4160_ = 2;
if (v_isShared_4157_ == 0)
{
v___x_4162_ = v___x_4156_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 0, v_foApprox_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 1, v_ctxApprox_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 2, v_quasiPatternApprox_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 3, v_constApprox_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 4, v_isDefEqStuckEx_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 5, v_unificationHints_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 6, v_proofIrrelevance_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 7, v_assignSyntheticOpaque_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 8, v_offsetCnstrs_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 9, v_transparency_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 11, v_univApprox_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 17, v_zetaUnused_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4184_, 19, v_canUnfoldPredicateConfig_4154_);
v___x_4162_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
uint8_t v_trackZetaDelta_4163_; lean_object* v_zetaDeltaSet_4164_; lean_object* v_lctx_4165_; lean_object* v_localInstances_4166_; lean_object* v_defEqCtx_x3f_4167_; lean_object* v_synthPendingDepth_4168_; lean_object* v_customCanUnfoldPredicate_x3f_4169_; uint8_t v_univApprox_4170_; uint8_t v_inTypeClassResolution_4171_; uint8_t v_cacheInferType_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4182_; 
lean_ctor_set_uint8(v___x_4162_, 10, v___x_4159_);
lean_ctor_set_uint8(v___x_4162_, 12, v___x_4158_);
lean_ctor_set_uint8(v___x_4162_, 13, v___x_4158_);
lean_ctor_set_uint8(v___x_4162_, 14, v___x_4160_);
lean_ctor_set_uint8(v___x_4162_, 15, v___x_4158_);
lean_ctor_set_uint8(v___x_4162_, 16, v___x_4158_);
lean_ctor_set_uint8(v___x_4162_, 18, v___x_4158_);
v_trackZetaDelta_4163_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*7);
v_zetaDeltaSet_4164_ = lean_ctor_get(v___y_4135_, 1);
v_lctx_4165_ = lean_ctor_get(v___y_4135_, 2);
v_localInstances_4166_ = lean_ctor_get(v___y_4135_, 3);
v_defEqCtx_x3f_4167_ = lean_ctor_get(v___y_4135_, 4);
v_synthPendingDepth_4168_ = lean_ctor_get(v___y_4135_, 5);
v_customCanUnfoldPredicate_x3f_4169_ = lean_ctor_get(v___y_4135_, 6);
v_univApprox_4170_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4171_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*7 + 2);
v_cacheInferType_4172_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*7 + 3);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4135_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v___y_4135_, 0);
lean_dec(v_unused_4183_);
v___x_4174_ = v___y_4135_;
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4169_);
lean_inc(v_synthPendingDepth_4168_);
lean_inc(v_defEqCtx_x3f_4167_);
lean_inc(v_localInstances_4166_);
lean_inc(v_lctx_4165_);
lean_inc(v_zetaDeltaSet_4164_);
lean_dec(v___y_4135_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4182_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
uint64_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4162_);
v___x_4177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4177_, 0, v___x_4162_);
lean_ctor_set_uint64(v___x_4177_, sizeof(void*)*1, v___x_4176_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4177_);
v___x_4179_ = v___x_4174_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_zetaDeltaSet_4164_);
lean_ctor_set(v_reuseFailAlloc_4181_, 2, v_lctx_4165_);
lean_ctor_set(v_reuseFailAlloc_4181_, 3, v_localInstances_4166_);
lean_ctor_set(v_reuseFailAlloc_4181_, 4, v_defEqCtx_x3f_4167_);
lean_ctor_set(v_reuseFailAlloc_4181_, 5, v_synthPendingDepth_4168_);
lean_ctor_set(v_reuseFailAlloc_4181_, 6, v_customCanUnfoldPredicate_x3f_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4181_, sizeof(void*)*7, v_trackZetaDelta_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4181_, sizeof(void*)*7 + 1, v_univApprox_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4181_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4181_, sizeof(void*)*7 + 3, v_cacheInferType_4172_);
v___x_4179_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; 
v___x_4180_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4134_, v___x_4179_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec_ref(v___x_4179_);
return v___x_4180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___y_4215_; lean_object* v_toCold_4232_; lean_object* v_currRecDepth_4233_; lean_object* v_ref_4234_; uint16_t v_optionFlags_4235_; uint8_t v_suppressElabErrors_4236_; uint8_t v_checkDeprecated_4237_; uint8_t v_isRecordingDeps_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4278_; 
v_toCold_4232_ = lean_ctor_get(v_a_4211_, 0);
v_currRecDepth_4233_ = lean_ctor_get(v_a_4211_, 1);
v_ref_4234_ = lean_ctor_get(v_a_4211_, 2);
v_optionFlags_4235_ = lean_ctor_get_uint16(v_a_4211_, sizeof(void*)*3);
v_suppressElabErrors_4236_ = lean_ctor_get_uint8(v_a_4211_, sizeof(void*)*3 + 2);
v_checkDeprecated_4237_ = lean_ctor_get_uint8(v_a_4211_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4238_ = lean_ctor_get_uint8(v_a_4211_, sizeof(void*)*3 + 4);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_a_4211_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4240_ = v_a_4211_;
v_isShared_4241_ = v_isSharedCheck_4278_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_ref_4234_);
lean_inc(v_currRecDepth_4233_);
lean_inc(v_toCold_4232_);
lean_dec(v_a_4211_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4278_;
goto v_resetjp_4239_;
}
v___jp_4214_:
{
if (lean_obj_tag(v___y_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
v_a_4216_ = lean_ctor_get(v___y_4215_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___y_4215_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___y_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___y_4215_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___y_4215_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___y_4215_);
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
v_resetjp_4239_:
{
lean_object* v_maxRecDepth_4242_; lean_object* v___x_4274_; uint8_t v___x_4275_; 
v_maxRecDepth_4242_ = lean_ctor_get(v_toCold_4232_, 3);
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = lean_nat_dec_eq(v_maxRecDepth_4242_, v___x_4274_);
if (v___x_4275_ == 0)
{
uint8_t v___x_4276_; 
v___x_4276_ = lean_nat_dec_eq(v_currRecDepth_4233_, v_maxRecDepth_4242_);
if (v___x_4276_ == 0)
{
goto v___jp_4243_;
}
else
{
lean_object* v___x_4277_; 
lean_del_object(v___x_4240_);
lean_dec(v_currRecDepth_4233_);
lean_dec_ref(v_toCold_4232_);
lean_dec(v_a_4212_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec_ref(v_e_4208_);
v___x_4277_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4234_);
return v___x_4277_;
}
}
else
{
goto v___jp_4243_;
}
v___jp_4243_:
{
lean_object* v___x_4244_; uint8_t v_transparency_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4244_ = l_Lean_Meta_Context_config(v_a_4209_);
v_transparency_4245_ = lean_ctor_get_uint8(v___x_4244_, 9);
lean_dec_ref(v___x_4244_);
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_nat_add(v_currRecDepth_4233_, v___x_4246_);
lean_dec(v_currRecDepth_4233_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 1, v___x_4247_);
v___x_4249_ = v___x_4240_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_toCold_4232_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_ref_4234_);
lean_ctor_set_uint16(v_reuseFailAlloc_4273_, sizeof(void*)*3, v_optionFlags_4235_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*3 + 2, v_suppressElabErrors_4236_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*3 + 3, v_checkDeprecated_4237_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*3 + 4, v_isRecordingDeps_4238_);
v___x_4249_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
uint8_t v___x_4250_; uint8_t v___x_4251_; 
v___x_4250_ = 1;
v___x_4251_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4245_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4208_, v_a_4209_, v_a_4210_, v___x_4249_, v_a_4212_);
lean_dec(v_a_4212_);
lean_dec_ref(v___x_4249_);
lean_dec(v_a_4210_);
v___y_4215_ = v___x_4252_;
goto v___jp_4214_;
}
else
{
lean_object* v_keyedConfig_4253_; uint8_t v_trackZetaDelta_4254_; lean_object* v_zetaDeltaSet_4255_; lean_object* v_lctx_4256_; lean_object* v_localInstances_4257_; lean_object* v_defEqCtx_x3f_4258_; lean_object* v_synthPendingDepth_4259_; lean_object* v_customCanUnfoldPredicate_x3f_4260_; uint8_t v_univApprox_4261_; uint8_t v_inTypeClassResolution_4262_; uint8_t v_cacheInferType_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4272_; 
v_keyedConfig_4253_ = lean_ctor_get(v_a_4209_, 0);
v_trackZetaDelta_4254_ = lean_ctor_get_uint8(v_a_4209_, sizeof(void*)*7);
v_zetaDeltaSet_4255_ = lean_ctor_get(v_a_4209_, 1);
v_lctx_4256_ = lean_ctor_get(v_a_4209_, 2);
v_localInstances_4257_ = lean_ctor_get(v_a_4209_, 3);
v_defEqCtx_x3f_4258_ = lean_ctor_get(v_a_4209_, 4);
v_synthPendingDepth_4259_ = lean_ctor_get(v_a_4209_, 5);
v_customCanUnfoldPredicate_x3f_4260_ = lean_ctor_get(v_a_4209_, 6);
v_univApprox_4261_ = lean_ctor_get_uint8(v_a_4209_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4262_ = lean_ctor_get_uint8(v_a_4209_, sizeof(void*)*7 + 2);
v_cacheInferType_4263_ = lean_ctor_get_uint8(v_a_4209_, sizeof(void*)*7 + 3);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_a_4209_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4265_ = v_a_4209_;
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4260_);
lean_inc(v_synthPendingDepth_4259_);
lean_inc(v_defEqCtx_x3f_4258_);
lean_inc(v_localInstances_4257_);
lean_inc(v_lctx_4256_);
lean_inc(v_zetaDeltaSet_4255_);
lean_inc(v_keyedConfig_4253_);
lean_dec(v_a_4209_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4267_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4250_, v_keyedConfig_4253_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4267_);
v___x_4269_ = v___x_4265_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_zetaDeltaSet_4255_);
lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_lctx_4256_);
lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_localInstances_4257_);
lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_defEqCtx_x3f_4258_);
lean_ctor_set(v_reuseFailAlloc_4271_, 5, v_synthPendingDepth_4259_);
lean_ctor_set(v_reuseFailAlloc_4271_, 6, v_customCanUnfoldPredicate_x3f_4260_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*7, v_trackZetaDelta_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*7 + 1, v_univApprox_4261_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*7 + 3, v_cacheInferType_4263_);
v___x_4269_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; 
v___x_4270_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4208_, v___x_4269_, v_a_4210_, v___x_4249_, v_a_4212_);
lean_dec(v_a_4212_);
lean_dec_ref(v___x_4249_);
lean_dec(v_a_4210_);
v___y_4215_ = v___x_4270_;
goto v___jp_4214_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = lean_infer_type(v_e_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
return v_res_4285_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_4286_){
_start:
{
switch(lean_obj_tag(v_x_4286_))
{
case 0:
{
uint8_t v___x_4287_; 
v___x_4287_ = 1;
return v___x_4287_;
}
case 2:
{
lean_object* v_a_4288_; lean_object* v_a_4289_; uint8_t v___x_4290_; 
v_a_4288_ = lean_ctor_get(v_x_4286_, 0);
v_a_4289_ = lean_ctor_get(v_x_4286_, 1);
v___x_4290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4288_);
if (v___x_4290_ == 0)
{
return v___x_4290_;
}
else
{
v_x_4286_ = v_a_4289_;
goto _start;
}
}
case 3:
{
lean_object* v_a_4292_; 
v_a_4292_ = lean_ctor_get(v_x_4286_, 1);
v_x_4286_ = v_a_4292_;
goto _start;
}
default: 
{
uint8_t v___x_4294_; 
v___x_4294_ = 0;
return v___x_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_4295_){
_start:
{
uint8_t v_res_4296_; lean_object* v_r_4297_; 
v_res_4296_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_4295_);
lean_dec(v_x_4295_);
v_r_4297_ = lean_box(v_res_4296_);
return v_r_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v_mctx_4302_; lean_object* v___x_4303_; lean_object* v_fst_4304_; lean_object* v_snd_4305_; lean_object* v___x_4306_; lean_object* v_cache_4307_; lean_object* v_zetaDeltaFVarIds_4308_; lean_object* v_postponed_4309_; lean_object* v_diag_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4319_; 
v___x_4301_ = lean_st_ref_get(v___y_4299_);
v_mctx_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc_ref(v_mctx_4302_);
lean_dec(v___x_4301_);
v___x_4303_ = lean_instantiate_level_mvars(v_mctx_4302_, v_l_4298_);
v_fst_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_fst_4304_);
v_snd_4305_ = lean_ctor_get(v___x_4303_, 1);
lean_inc(v_snd_4305_);
lean_dec_ref(v___x_4303_);
v___x_4306_ = lean_st_ref_take(v___y_4299_);
v_cache_4307_ = lean_ctor_get(v___x_4306_, 1);
v_zetaDeltaFVarIds_4308_ = lean_ctor_get(v___x_4306_, 2);
v_postponed_4309_ = lean_ctor_get(v___x_4306_, 3);
v_diag_4310_ = lean_ctor_get(v___x_4306_, 4);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; 
v_unused_4320_ = lean_ctor_get(v___x_4306_, 0);
lean_dec(v_unused_4320_);
v___x_4312_ = v___x_4306_;
v_isShared_4313_ = v_isSharedCheck_4319_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_diag_4310_);
lean_inc(v_postponed_4309_);
lean_inc(v_zetaDeltaFVarIds_4308_);
lean_inc(v_cache_4307_);
lean_dec(v___x_4306_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4319_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 0, v_fst_4304_);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_fst_4304_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_cache_4307_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_zetaDeltaFVarIds_4308_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_postponed_4309_);
lean_ctor_set(v_reuseFailAlloc_4318_, 4, v_diag_4310_);
v___x_4315_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = lean_st_ref_put(v___y_4299_, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v_snd_4305_);
return v___x_4317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4321_, v___y_4322_);
lean_dec(v___y_4322_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4325_, v___y_4327_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_00_u03c3_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v___y_4352_; 
switch(lean_obj_tag(v_x_4340_))
{
case 3:
{
lean_object* v_u_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_u_4373_ = lean_ctor_get(v_x_4340_, 0);
lean_inc(v_u_4373_);
lean_dec_ref_known(v_x_4340_, 1);
v___x_4374_ = lean_unsigned_to_nat(0u);
v___x_4375_ = lean_nat_dec_eq(v_x_4341_, v___x_4374_);
lean_dec(v_x_4341_);
if (v___x_4375_ == 0)
{
lean_dec(v_u_4373_);
lean_dec_ref(v_00_u03c3_4339_);
goto v___jp_4347_;
}
else
{
lean_object* v_paramNames_4376_; lean_object* v_lvls_4377_; uint8_t v___x_4378_; 
v_paramNames_4376_ = lean_ctor_get(v_00_u03c3_4339_, 0);
lean_inc(v_paramNames_4376_);
v_lvls_4377_ = lean_ctor_get(v_00_u03c3_4339_, 1);
lean_inc(v_lvls_4377_);
lean_dec_ref(v_00_u03c3_4339_);
v___x_4378_ = l_List_isEmpty___redArg(v_paramNames_4376_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_Level_instantiateParams(v_u_4373_, v_paramNames_4376_, v_lvls_4377_);
v___y_4352_ = v___x_4379_;
goto v___jp_4351_;
}
else
{
lean_dec(v_lvls_4377_);
lean_dec(v_paramNames_4376_);
v___y_4352_ = v_u_4373_;
goto v___jp_4351_;
}
}
}
case 7:
{
lean_object* v_body_4380_; lean_object* v_zero_4381_; uint8_t v_isZero_4382_; 
v_body_4380_ = lean_ctor_get(v_x_4340_, 2);
lean_inc_ref(v_body_4380_);
lean_dec_ref_known(v_x_4340_, 3);
v_zero_4381_ = lean_unsigned_to_nat(0u);
v_isZero_4382_ = lean_nat_dec_eq(v_x_4341_, v_zero_4381_);
if (v_isZero_4382_ == 1)
{
uint8_t v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
lean_dec_ref(v_body_4380_);
lean_dec(v_x_4341_);
lean_dec_ref(v_00_u03c3_4339_);
v___x_4383_ = 0;
v___x_4384_ = lean_box(v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
else
{
lean_object* v_one_4386_; lean_object* v_n_4387_; 
v_one_4386_ = lean_unsigned_to_nat(1u);
v_n_4387_ = lean_nat_sub(v_x_4341_, v_one_4386_);
lean_dec(v_x_4341_);
v_x_4340_ = v_body_4380_;
v_x_4341_ = v_n_4387_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4389_; 
v_body_4389_ = lean_ctor_get(v_x_4340_, 3);
lean_inc_ref(v_body_4389_);
lean_dec_ref_known(v_x_4340_, 4);
v_x_4340_ = v_body_4389_;
goto _start;
}
case 10:
{
lean_object* v_expr_4391_; 
v_expr_4391_ = lean_ctor_get(v_x_4340_, 1);
lean_inc_ref(v_expr_4391_);
lean_dec_ref_known(v_x_4340_, 2);
v_x_4340_ = v_expr_4391_;
goto _start;
}
default: 
{
lean_dec(v_x_4341_);
lean_dec_ref(v_x_4340_);
lean_dec_ref(v_00_u03c3_4339_);
goto v___jp_4347_;
}
}
v___jp_4347_:
{
uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = 2;
v___x_4349_ = lean_box(v___x_4348_);
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
return v___x_4350_;
}
v___jp_4351_:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v___y_4352_, v_a_4343_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4364_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
uint8_t v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
v___x_4358_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4354_);
lean_dec(v_a_4354_);
v___x_4359_ = l_Lean_Bool_toLBool(v___x_4358_);
v___x_4360_ = lean_box(v___x_4359_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4360_);
v___x_4362_ = v___x_4356_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_a_4365_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4353_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4353_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_00_u03c3_4393_, lean_object* v_x_4394_, lean_object* v_x_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_00_u03c3_4393_, v_x_4394_, v_x_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_);
lean_dec(v_a_4399_);
lean_dec_ref(v_a_4398_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object* v_00_u03c3_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
if (lean_obj_tag(v_a_4403_) == 0)
{
lean_object* v___x_4405_; 
lean_dec_ref(v_00_u03c3_4402_);
v___x_4405_ = l_List_reverse___redArg(v_a_4404_);
return v___x_4405_;
}
else
{
lean_object* v_head_4406_; lean_object* v_tail_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4421_; 
v_head_4406_ = lean_ctor_get(v_a_4403_, 0);
v_tail_4407_ = lean_ctor_get(v_a_4403_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_a_4403_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4409_ = v_a_4403_;
v_isShared_4410_ = v_isSharedCheck_4421_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_tail_4407_);
lean_inc(v_head_4406_);
lean_dec(v_a_4403_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4421_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___y_4412_; lean_object* v_paramNames_4417_; lean_object* v_lvls_4418_; uint8_t v___x_4419_; 
v_paramNames_4417_ = lean_ctor_get(v_00_u03c3_4402_, 0);
v_lvls_4418_ = lean_ctor_get(v_00_u03c3_4402_, 1);
v___x_4419_ = l_List_isEmpty___redArg(v_paramNames_4417_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; 
lean_inc(v_lvls_4418_);
lean_inc(v_paramNames_4417_);
v___x_4420_ = l_Lean_Level_instantiateParams(v_head_4406_, v_paramNames_4417_, v_lvls_4418_);
v___y_4412_ = v___x_4420_;
goto v___jp_4411_;
}
else
{
v___y_4412_ = v_head_4406_;
goto v___jp_4411_;
}
v___jp_4411_:
{
lean_object* v___x_4414_; 
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 1, v_a_4404_);
lean_ctor_set(v___x_4409_, 0, v___y_4412_);
v___x_4414_ = v___x_4409_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___y_4412_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_a_4404_);
v___x_4414_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
v_a_4403_ = v_tail_4407_;
v_a_4404_ = v___x_4414_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_00_u03c3_4424_, lean_object* v_x_4425_, lean_object* v_x_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
switch(lean_obj_tag(v_x_4425_))
{
case 4:
{
lean_object* v_declName_4432_; lean_object* v_us_4433_; lean_object* v___y_4435_; lean_object* v_paramNames_4449_; uint8_t v___x_4450_; 
v_declName_4432_ = lean_ctor_get(v_x_4425_, 0);
lean_inc(v_declName_4432_);
v_us_4433_ = lean_ctor_get(v_x_4425_, 1);
lean_inc(v_us_4433_);
lean_dec_ref_known(v_x_4425_, 2);
v_paramNames_4449_ = lean_ctor_get(v_00_u03c3_4424_, 0);
v___x_4450_ = l_List_isEmpty___redArg(v_paramNames_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4451_ = lean_box(0);
v___x_4452_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4424_, v_us_4433_, v___x_4451_);
v___y_4435_ = v___x_4452_;
goto v___jp_4434_;
}
else
{
lean_dec_ref(v_00_u03c3_4424_);
v___y_4435_ = v_us_4433_;
goto v___jp_4434_;
}
v___jp_4434_:
{
lean_object* v___x_4436_; 
v___x_4436_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4432_, v___y_4435_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v_fst_4438_; lean_object* v_snd_4439_; lean_object* v___x_4440_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_a_4437_);
lean_dec_ref_known(v___x_4436_, 1);
v_fst_4438_ = lean_ctor_get(v_a_4437_, 0);
lean_inc(v_fst_4438_);
v_snd_4439_ = lean_ctor_get(v_a_4437_, 1);
lean_inc(v_snd_4439_);
lean_dec(v_a_4437_);
v___x_4440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4439_, v_fst_4438_, v_x_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
return v___x_4440_;
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_x_4426_);
v_a_4441_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4436_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4436_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_4453_; lean_object* v___x_4454_; 
lean_dec_ref(v_00_u03c3_4424_);
v_fvarId_4453_ = lean_ctor_get(v_x_4425_, 0);
lean_inc(v_fvarId_4453_);
lean_dec_ref_known(v_x_4425_, 1);
v___x_4454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4453_, v_a_4427_, v_a_4429_, v_a_4430_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v___x_4456_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4457_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4456_, v_a_4455_, v_x_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
return v___x_4457_;
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec(v_x_4426_);
v_a_4458_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4454_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4454_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4466_; lean_object* v___x_4467_; 
lean_dec_ref(v_00_u03c3_4424_);
v_mvarId_4466_ = lean_ctor_get(v_x_4425_, 0);
lean_inc(v_mvarId_4466_);
lean_dec_ref_known(v_x_4425_, 1);
v___x_4467_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4466_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref_known(v___x_4467_, 1);
v___x_4469_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4470_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4469_, v_a_4468_, v_x_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_);
return v___x_4470_;
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_x_4426_);
v_a_4471_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4467_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4467_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
case 5:
{
lean_object* v_fn_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_fn_4479_ = lean_ctor_get(v_x_4425_, 0);
lean_inc_ref(v_fn_4479_);
lean_dec_ref_known(v_x_4425_, 2);
v___x_4480_ = lean_unsigned_to_nat(1u);
v___x_4481_ = lean_nat_add(v_x_4426_, v___x_4480_);
lean_dec(v_x_4426_);
v_x_4425_ = v_fn_4479_;
v_x_4426_ = v___x_4481_;
goto _start;
}
case 10:
{
lean_object* v_expr_4483_; 
v_expr_4483_ = lean_ctor_get(v_x_4425_, 1);
lean_inc_ref(v_expr_4483_);
lean_dec_ref_known(v_x_4425_, 2);
v_x_4425_ = v_expr_4483_;
goto _start;
}
case 8:
{
lean_object* v_body_4485_; 
v_body_4485_ = lean_ctor_get(v_x_4425_, 3);
lean_inc_ref(v_body_4485_);
lean_dec_ref_known(v_x_4425_, 4);
v_x_4425_ = v_body_4485_;
goto _start;
}
case 6:
{
lean_object* v_body_4487_; lean_object* v_zero_4488_; uint8_t v_isZero_4489_; 
v_body_4487_ = lean_ctor_get(v_x_4425_, 2);
lean_inc_ref(v_body_4487_);
lean_dec_ref_known(v_x_4425_, 3);
v_zero_4488_ = lean_unsigned_to_nat(0u);
v_isZero_4489_ = lean_nat_dec_eq(v_x_4426_, v_zero_4488_);
if (v_isZero_4489_ == 1)
{
uint8_t v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
lean_dec_ref(v_body_4487_);
lean_dec(v_x_4426_);
lean_dec_ref(v_00_u03c3_4424_);
v___x_4490_ = 0;
v___x_4491_ = lean_box(v___x_4490_);
v___x_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
return v___x_4492_;
}
else
{
lean_object* v_one_4493_; lean_object* v_n_4494_; 
v_one_4493_ = lean_unsigned_to_nat(1u);
v_n_4494_ = lean_nat_sub(v_x_4426_, v_one_4493_);
lean_dec(v_x_4426_);
v_x_4425_ = v_body_4487_;
v_x_4426_ = v_n_4494_;
goto _start;
}
}
default: 
{
uint8_t v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec(v_x_4426_);
lean_dec_ref(v_x_4425_);
lean_dec_ref(v_00_u03c3_4424_);
v___x_4496_ = 2;
v___x_4497_ = lean_box(v___x_4496_);
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
return v___x_4498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_00_u03c3_4499_, lean_object* v_x_4500_, lean_object* v_x_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4499_, v_x_4500_, v_x_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object* v_00_u03c3_4508_, lean_object* v_x_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
switch(lean_obj_tag(v_x_4509_))
{
case 1:
{
lean_object* v_fvarId_4515_; lean_object* v___x_4516_; 
lean_dec_ref(v_00_u03c3_4508_);
v_fvarId_4515_ = lean_ctor_get(v_x_4509_, 0);
lean_inc(v_fvarId_4515_);
lean_dec_ref_known(v_x_4509_, 1);
v___x_4516_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4515_, v_a_4510_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4516_, 1);
v___x_4518_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4519_ = lean_unsigned_to_nat(0u);
v___x_4520_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4518_, v_a_4517_, v___x_4519_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
return v___x_4520_;
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
v_a_4521_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4516_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4516_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4529_; lean_object* v___x_4530_; 
lean_dec_ref(v_00_u03c3_4508_);
v_mvarId_4529_ = lean_ctor_get(v_x_4509_, 0);
lean_inc(v_mvarId_4529_);
lean_dec_ref_known(v_x_4509_, 1);
v___x_4530_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4529_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref_known(v___x_4530_, 1);
v___x_4532_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4532_, v_a_4531_, v___x_4533_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
return v___x_4534_;
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
v_a_4535_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4530_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4530_);
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
case 3:
{
uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
lean_dec_ref_known(v_x_4509_, 1);
lean_dec_ref(v_00_u03c3_4508_);
v___x_4543_ = 0;
v___x_4544_ = lean_box(v___x_4543_);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
return v___x_4545_;
}
case 4:
{
lean_object* v_declName_4546_; lean_object* v_us_4547_; lean_object* v___y_4549_; lean_object* v_paramNames_4564_; uint8_t v___x_4565_; 
v_declName_4546_ = lean_ctor_get(v_x_4509_, 0);
lean_inc(v_declName_4546_);
v_us_4547_ = lean_ctor_get(v_x_4509_, 1);
lean_inc(v_us_4547_);
lean_dec_ref_known(v_x_4509_, 2);
v_paramNames_4564_ = lean_ctor_get(v_00_u03c3_4508_, 0);
v___x_4565_ = l_List_isEmpty___redArg(v_paramNames_4564_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = lean_box(0);
v___x_4567_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4508_, v_us_4547_, v___x_4566_);
v___y_4549_ = v___x_4567_;
goto v___jp_4548_;
}
else
{
lean_dec_ref(v_00_u03c3_4508_);
v___y_4549_ = v_us_4547_;
goto v___jp_4548_;
}
v___jp_4548_:
{
lean_object* v___x_4550_; 
v___x_4550_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4546_, v___y_4549_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v_fst_4552_; lean_object* v_snd_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v_fst_4552_ = lean_ctor_get(v_a_4551_, 0);
lean_inc(v_fst_4552_);
v_snd_4553_ = lean_ctor_get(v_a_4551_, 1);
lean_inc(v_snd_4553_);
lean_dec(v_a_4551_);
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4553_, v_fst_4552_, v___x_4554_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
return v___x_4555_;
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_a_4556_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4550_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4550_);
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
}
case 5:
{
lean_object* v_fn_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v_fn_4568_ = lean_ctor_get(v_x_4509_, 0);
lean_inc_ref(v_fn_4568_);
lean_dec_ref_known(v_x_4509_, 2);
v___x_4569_ = lean_unsigned_to_nat(1u);
v___x_4570_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4508_, v_fn_4568_, v___x_4569_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
return v___x_4570_;
}
case 6:
{
uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec_ref_known(v_x_4509_, 3);
lean_dec_ref(v_00_u03c3_4508_);
v___x_4571_ = 0;
v___x_4572_ = lean_box(v___x_4571_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
case 7:
{
lean_object* v_body_4574_; 
v_body_4574_ = lean_ctor_get(v_x_4509_, 2);
lean_inc_ref(v_body_4574_);
lean_dec_ref_known(v_x_4509_, 3);
v_x_4509_ = v_body_4574_;
goto _start;
}
case 8:
{
lean_object* v_body_4576_; 
v_body_4576_ = lean_ctor_get(v_x_4509_, 3);
lean_inc_ref(v_body_4576_);
lean_dec_ref_known(v_x_4509_, 4);
v_x_4509_ = v_body_4576_;
goto _start;
}
case 9:
{
uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
lean_dec_ref_known(v_x_4509_, 1);
lean_dec_ref(v_00_u03c3_4508_);
v___x_4578_ = 0;
v___x_4579_ = lean_box(v___x_4578_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
case 10:
{
lean_object* v_expr_4581_; 
v_expr_4581_ = lean_ctor_get(v_x_4509_, 1);
lean_inc_ref(v_expr_4581_);
lean_dec_ref_known(v_x_4509_, 2);
v_x_4509_ = v_expr_4581_;
goto _start;
}
default: 
{
uint8_t v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
lean_dec_ref(v_x_4509_);
lean_dec_ref(v_00_u03c3_4508_);
v___x_4583_ = 2;
v___x_4584_ = lean_box(v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object* v_00_u03c3_4586_, lean_object* v_x_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4586_, v_x_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_e_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4601_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v___x_4600_, v_e_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_e_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_Meta_isPropQuick(v_e_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v___x_4615_; 
lean_inc_ref(v_e_4609_);
v___x_4615_ = l_Lean_Meta_isPropQuick(v_e_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4672_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4672_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4672_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
uint8_t v___x_4620_; 
v___x_4620_ = lean_unbox(v_a_4616_);
lean_dec(v_a_4616_);
switch(v___x_4620_)
{
case 0:
{
uint8_t v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
lean_dec_ref(v_e_4609_);
v___x_4621_ = 0;
v___x_4622_ = lean_box(v___x_4621_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4622_);
v___x_4624_ = v___x_4618_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
case 1:
{
uint8_t v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4629_; 
lean_dec_ref(v_e_4609_);
v___x_4626_ = 1;
v___x_4627_ = lean_box(v___x_4626_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4627_);
v___x_4629_ = v___x_4618_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
default: 
{
lean_object* v___x_4631_; 
lean_del_object(v___x_4618_);
lean_inc(v_a_4613_);
lean_inc_ref(v_a_4612_);
lean_inc(v_a_4611_);
lean_inc_ref(v_a_4610_);
v___x_4631_ = lean_infer_type(v_e_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = l_Lean_Meta_whnfD(v_a_4632_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4655_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4655_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4655_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
if (lean_obj_tag(v_a_4634_) == 3)
{
lean_object* v_u_4638_; lean_object* v___x_4639_; lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4649_; 
lean_del_object(v___x_4636_);
v_u_4638_ = lean_ctor_get(v_a_4634_, 0);
lean_inc(v_u_4638_);
lean_dec_ref_known(v_a_4634_, 1);
v___x_4639_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4638_, v_a_4611_);
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4642_ = v___x_4639_;
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4639_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
uint8_t v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4640_);
lean_dec(v_a_4640_);
v___x_4645_ = lean_box(v___x_4644_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 0, v___x_4645_);
v___x_4647_ = v___x_4642_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
else
{
uint8_t v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4653_; 
lean_dec(v_a_4634_);
v___x_4650_ = 0;
v___x_4651_ = lean_box(v___x_4650_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4651_);
v___x_4653_ = v___x_4636_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4651_);
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
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
v_a_4656_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4633_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4633_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
v_a_4664_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4631_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4631_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v_e_4609_);
v_a_4673_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4615_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4615_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_Meta_isProp(v_e_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4688_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_obj_tag_nat(v_x_4688_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4690_);
lean_dec(v_x_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4692_, lean_object* v_k_4693_){
_start:
{
if (lean_obj_tag(v_t_4692_) == 3)
{
lean_object* v_idx_4694_; lean_object* v_numArgs_4695_; lean_object* v___x_4696_; 
v_idx_4694_ = lean_ctor_get(v_t_4692_, 0);
lean_inc(v_idx_4694_);
v_numArgs_4695_ = lean_ctor_get(v_t_4692_, 1);
lean_inc(v_numArgs_4695_);
lean_dec_ref_known(v_t_4692_, 2);
v___x_4696_ = lean_apply_2(v_k_4693_, v_idx_4694_, v_numArgs_4695_);
return v___x_4696_;
}
else
{
lean_dec(v_t_4692_);
return v_k_4693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4697_, lean_object* v_ctorIdx_4698_, lean_object* v_t_4699_, lean_object* v_h_4700_, lean_object* v_k_4701_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4699_, v_k_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4703_, lean_object* v_ctorIdx_4704_, lean_object* v_t_4705_, lean_object* v_h_4706_, lean_object* v_k_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4703_, v_ctorIdx_4704_, v_t_4705_, v_h_4706_, v_k_4707_);
lean_dec(v_ctorIdx_4704_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4709_, lean_object* v_false_4710_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4709_, v_false_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4712_, lean_object* v_t_4713_, lean_object* v_h_4714_, lean_object* v_false_4715_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4713_, v_false_4715_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4717_, lean_object* v_true_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4717_, v_true_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4720_, lean_object* v_t_4721_, lean_object* v_h_4722_, lean_object* v_true_4723_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4721_, v_true_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4725_, lean_object* v_undef_4726_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4725_, v_undef_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4728_, lean_object* v_t_4729_, lean_object* v_h_4730_, lean_object* v_undef_4731_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4729_, v_undef_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4733_, lean_object* v_bvar_4734_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4733_, v_bvar_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4736_, lean_object* v_t_4737_, lean_object* v_h_4738_, lean_object* v_bvar_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4737_, v_bvar_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4741_){
_start:
{
switch(v_x_4741_)
{
case 0:
{
lean_object* v___x_4742_; 
v___x_4742_ = lean_box(0);
return v___x_4742_;
}
case 1:
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_box(1);
return v___x_4743_;
}
default: 
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_box(2);
return v___x_4744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4745_){
_start:
{
uint8_t v_x_25__boxed_4746_; lean_object* v_res_4747_; 
v_x_25__boxed_4746_ = lean_unbox(v_x_4745_);
v_res_4747_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4746_);
return v_res_4747_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4748_){
_start:
{
switch(lean_obj_tag(v_x_4748_))
{
case 0:
{
uint8_t v___x_4749_; 
v___x_4749_ = 0;
return v___x_4749_;
}
case 1:
{
uint8_t v___x_4750_; 
v___x_4750_ = 1;
return v___x_4750_;
}
default: 
{
uint8_t v___x_4751_; 
v___x_4751_ = 2;
return v___x_4751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4752_);
lean_dec(v_x_4752_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_00_u03c3_4756_, lean_object* v_e_4757_, lean_object* v_numArgs_4758_){
_start:
{
lean_object* v___y_4760_; 
switch(lean_obj_tag(v_e_4757_))
{
case 3:
{
lean_object* v_u_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v_u_4766_ = lean_ctor_get(v_e_4757_, 0);
lean_inc(v_u_4766_);
lean_dec_ref_known(v_e_4757_, 1);
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = lean_nat_dec_eq(v_numArgs_4758_, v___x_4767_);
lean_dec(v_numArgs_4758_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; 
lean_dec(v_u_4766_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4769_ = lean_box(2);
return v___x_4769_;
}
else
{
lean_object* v_paramNames_4770_; lean_object* v_lvls_4771_; uint8_t v___x_4772_; 
v_paramNames_4770_ = lean_ctor_get(v_00_u03c3_4756_, 0);
lean_inc(v_paramNames_4770_);
v_lvls_4771_ = lean_ctor_get(v_00_u03c3_4756_, 1);
lean_inc(v_lvls_4771_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4772_ = l_List_isEmpty___redArg(v_paramNames_4770_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Level_instantiateParams(v_u_4766_, v_paramNames_4770_, v_lvls_4771_);
v___y_4760_ = v___x_4773_;
goto v___jp_4759_;
}
else
{
lean_dec(v_lvls_4771_);
lean_dec(v_paramNames_4770_);
v___y_4760_ = v_u_4766_;
goto v___jp_4759_;
}
}
}
case 7:
{
lean_object* v_body_4774_; lean_object* v_zero_4775_; uint8_t v_isZero_4776_; 
v_body_4774_ = lean_ctor_get(v_e_4757_, 2);
lean_inc_ref(v_body_4774_);
lean_dec_ref_known(v_e_4757_, 3);
v_zero_4775_ = lean_unsigned_to_nat(0u);
v_isZero_4776_ = lean_nat_dec_eq(v_numArgs_4758_, v_zero_4775_);
if (v_isZero_4776_ == 0)
{
lean_object* v_one_4777_; lean_object* v_n_4778_; 
v_one_4777_ = lean_unsigned_to_nat(1u);
v_n_4778_ = lean_nat_sub(v_numArgs_4758_, v_one_4777_);
lean_dec(v_numArgs_4758_);
v_e_4757_ = v_body_4774_;
v_numArgs_4758_ = v_n_4778_;
goto _start;
}
else
{
lean_object* v___x_4780_; 
lean_dec_ref(v_body_4774_);
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4780_ = lean_box(2);
return v___x_4780_;
}
}
case 10:
{
lean_object* v_expr_4781_; 
v_expr_4781_ = lean_ctor_get(v_e_4757_, 1);
lean_inc_ref(v_expr_4781_);
lean_dec_ref_known(v_e_4757_, 2);
v_e_4757_ = v_expr_4781_;
goto _start;
}
case 5:
{
lean_object* v_fn_4783_; 
v_fn_4783_ = lean_ctor_get(v_e_4757_, 0);
if (lean_obj_tag(v_fn_4783_) == 4)
{
lean_object* v_declName_4784_; 
v_declName_4784_ = lean_ctor_get(v_fn_4783_, 0);
lean_inc(v_declName_4784_);
if (lean_obj_tag(v_declName_4784_) == 1)
{
lean_object* v_pre_4785_; 
v_pre_4785_ = lean_ctor_get(v_declName_4784_, 0);
if (lean_obj_tag(v_pre_4785_) == 0)
{
lean_object* v_arg_4786_; lean_object* v_str_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v_arg_4786_ = lean_ctor_get(v_e_4757_, 1);
lean_inc_ref(v_arg_4786_);
lean_dec_ref_known(v_e_4757_, 2);
v_str_4787_ = lean_ctor_get(v_declName_4784_, 1);
lean_inc_ref(v_str_4787_);
lean_dec_ref_known(v_declName_4784_, 2);
v___x_4788_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4789_ = lean_string_dec_eq(v_str_4787_, v___x_4788_);
lean_dec_ref(v_str_4787_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref(v_arg_4786_);
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4790_ = lean_box(2);
return v___x_4790_;
}
else
{
v_e_4757_ = v_arg_4786_;
goto _start;
}
}
else
{
lean_object* v___x_4792_; 
lean_dec_ref_known(v_declName_4784_, 2);
lean_dec_ref_known(v_e_4757_, 2);
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4792_ = lean_box(2);
return v___x_4792_;
}
}
else
{
lean_object* v___x_4793_; 
lean_dec(v_declName_4784_);
lean_dec_ref_known(v_e_4757_, 2);
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4793_ = lean_box(2);
return v___x_4793_;
}
}
else
{
lean_object* v___x_4794_; 
lean_dec_ref_known(v_e_4757_, 2);
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4794_ = lean_box(2);
return v___x_4794_;
}
}
default: 
{
lean_object* v___x_4795_; 
lean_dec(v_numArgs_4758_);
lean_dec_ref(v_e_4757_);
lean_dec_ref(v_00_u03c3_4756_);
v___x_4795_ = lean_box(2);
return v___x_4795_;
}
}
v___jp_4759_:
{
uint8_t v___x_4761_; 
v___x_4761_ = l_Lean_Level_isNeverZero(v___y_4760_);
if (v___x_4761_ == 0)
{
uint8_t v___x_4762_; 
v___x_4762_ = l_Lean_Level_isZero(v___y_4760_);
lean_dec(v___y_4760_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_box(2);
return v___x_4763_;
}
else
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_box(1);
return v___x_4764_;
}
}
else
{
lean_object* v___x_4765_; 
lean_dec(v___y_4760_);
v___x_4765_ = lean_box(0);
return v___x_4765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_00_u03c3_4796_, lean_object* v_r_4797_, lean_object* v_binderType_4798_){
_start:
{
if (lean_obj_tag(v_r_4797_) == 3)
{
lean_object* v_idx_4799_; lean_object* v_numArgs_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4812_; 
v_idx_4799_ = lean_ctor_get(v_r_4797_, 0);
v_numArgs_4800_ = lean_ctor_get(v_r_4797_, 1);
v_isSharedCheck_4812_ = !lean_is_exclusive(v_r_4797_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4802_ = v_r_4797_;
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_numArgs_4800_);
lean_inc(v_idx_4799_);
lean_dec(v_r_4797_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_zero_4804_; uint8_t v_isZero_4805_; 
v_zero_4804_ = lean_unsigned_to_nat(0u);
v_isZero_4805_ = lean_nat_dec_eq(v_idx_4799_, v_zero_4804_);
if (v_isZero_4805_ == 1)
{
lean_object* v___x_4806_; 
lean_del_object(v___x_4802_);
lean_dec(v_idx_4799_);
v___x_4806_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_00_u03c3_4796_, v_binderType_4798_, v_numArgs_4800_);
return v___x_4806_;
}
else
{
lean_object* v_one_4807_; lean_object* v_n_4808_; lean_object* v___x_4810_; 
lean_dec_ref(v_binderType_4798_);
lean_dec_ref(v_00_u03c3_4796_);
v_one_4807_ = lean_unsigned_to_nat(1u);
v_n_4808_ = lean_nat_sub(v_idx_4799_, v_one_4807_);
lean_dec(v_idx_4799_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_n_4808_);
v___x_4810_ = v___x_4802_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_n_4808_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_numArgs_4800_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_4798_);
lean_dec_ref(v_00_u03c3_4796_);
return v_r_4797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_00_u03c3_4813_, lean_object* v_x_4814_, lean_object* v_x_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v_type_4822_; lean_object* v___y_4823_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; 
switch(lean_obj_tag(v_x_4814_))
{
case 7:
{
lean_object* v_binderType_4854_; lean_object* v_body_4855_; lean_object* v_zero_4856_; uint8_t v_isZero_4857_; 
v_binderType_4854_ = lean_ctor_get(v_x_4814_, 1);
v_body_4855_ = lean_ctor_get(v_x_4814_, 2);
v_zero_4856_ = lean_unsigned_to_nat(0u);
v_isZero_4857_ = lean_nat_dec_eq(v_x_4815_, v_zero_4856_);
if (v_isZero_4857_ == 1)
{
v_type_4822_ = v_x_4814_;
v___y_4823_ = v_a_4816_;
v___y_4824_ = v_a_4817_;
v___y_4825_ = v_a_4818_;
v___y_4826_ = v_a_4819_;
goto v___jp_4821_;
}
else
{
lean_object* v_one_4858_; lean_object* v_n_4859_; lean_object* v___x_4860_; 
lean_inc_ref(v_body_4855_);
lean_inc_ref(v_binderType_4854_);
lean_dec_ref_known(v_x_4814_, 3);
v_one_4858_ = lean_unsigned_to_nat(1u);
v_n_4859_ = lean_nat_sub(v_x_4815_, v_one_4858_);
lean_inc_ref(v_00_u03c3_4813_);
v___x_4860_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4813_, v_body_4855_, v_n_4859_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
lean_dec(v_n_4859_);
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
v___x_4865_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4813_, v_a_4861_, v_binderType_4854_);
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
lean_dec_ref(v_binderType_4854_);
lean_dec_ref(v_00_u03c3_4813_);
return v___x_4860_;
}
}
}
case 8:
{
lean_object* v_type_4870_; lean_object* v_body_4871_; lean_object* v___x_4872_; 
v_type_4870_ = lean_ctor_get(v_x_4814_, 1);
lean_inc_ref(v_type_4870_);
v_body_4871_ = lean_ctor_get(v_x_4814_, 3);
lean_inc_ref(v_body_4871_);
lean_dec_ref_known(v_x_4814_, 4);
lean_inc_ref(v_00_u03c3_4813_);
v___x_4872_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4813_, v_body_4871_, v_x_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4881_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4875_ = v___x_4872_;
v_isShared_4876_ = v_isSharedCheck_4881_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4872_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4881_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4877_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4813_, v_a_4873_, v_type_4870_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 0, v___x_4877_);
v___x_4879_ = v___x_4875_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
else
{
lean_dec_ref(v_type_4870_);
lean_dec_ref(v_00_u03c3_4813_);
return v___x_4872_;
}
}
case 10:
{
lean_object* v_expr_4882_; 
v_expr_4882_ = lean_ctor_get(v_x_4814_, 1);
lean_inc_ref(v_expr_4882_);
lean_dec_ref_known(v_x_4814_, 2);
v_x_4814_ = v_expr_4882_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; 
lean_dec_ref(v_00_u03c3_4813_);
v_deBruijnIndex_4884_ = lean_ctor_get(v_x_4814_, 0);
lean_inc(v_deBruijnIndex_4884_);
lean_dec_ref_known(v_x_4814_, 1);
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = lean_nat_dec_eq(v_x_4815_, v___x_4885_);
if (v___x_4886_ == 0)
{
lean_dec(v_deBruijnIndex_4884_);
goto v___jp_4851_;
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4887_, 0, v_deBruijnIndex_4884_);
lean_ctor_set(v___x_4887_, 1, v___x_4885_);
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
return v___x_4888_;
}
}
default: 
{
lean_object* v___x_4889_; uint8_t v___x_4890_; 
v___x_4889_ = lean_unsigned_to_nat(0u);
v___x_4890_ = lean_nat_dec_eq(v_x_4815_, v___x_4889_);
if (v___x_4890_ == 0)
{
lean_dec_ref(v_x_4814_);
lean_dec_ref(v_00_u03c3_4813_);
goto v___jp_4851_;
}
else
{
v_type_4822_ = v_x_4814_;
v___y_4823_ = v_a_4816_;
v___y_4824_ = v_a_4817_;
v___y_4825_ = v_a_4818_;
v___y_4826_ = v_a_4819_;
goto v___jp_4821_;
}
}
}
v___jp_4821_:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_Expr_getAppFn(v_type_4822_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_deBruijnIndex_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
lean_dec_ref(v_00_u03c3_4813_);
v_deBruijnIndex_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_deBruijnIndex_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4829_ = l_Lean_Expr_getAppNumArgs(v_type_4822_);
lean_dec_ref(v_type_4822_);
v___x_4830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4830_, 0, v_deBruijnIndex_4828_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
else
{
lean_object* v___x_4832_; 
lean_dec_ref(v___x_4827_);
v___x_4832_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4813_, v_type_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4842_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4842_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4842_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
uint8_t v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4837_ = lean_unbox(v_a_4833_);
lean_dec(v_a_4833_);
v___x_4838_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4837_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4838_);
v___x_4840_ = v___x_4835_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4850_; 
v_a_4843_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4845_ = v___x_4832_;
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4832_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4848_; 
if (v_isShared_4846_ == 0)
{
v___x_4848_ = v___x_4845_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
v___jp_4851_:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4852_ = lean_box(2);
v___x_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
return v___x_4853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_00_u03c3_4891_, lean_object* v_x_4892_, lean_object* v_x_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4891_, v_x_4892_, v_x_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec(v_x_4893_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_00_u03c3_4900_, lean_object* v_e_4901_, lean_object* v_n_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4900_, v_e_4901_, v_n_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4918_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4918_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4918_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
uint8_t v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4913_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4909_);
lean_dec(v_a_4909_);
v___x_4914_ = lean_box(v___x_4913_);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4914_);
v___x_4916_ = v___x_4911_;
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
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
v_a_4919_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4908_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4908_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_00_u03c3_4927_, lean_object* v_e_4928_, lean_object* v_n_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_00_u03c3_4927_, v_e_4928_, v_n_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_n_4929_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
switch(lean_obj_tag(v_x_4936_))
{
case 1:
{
lean_object* v_fvarId_4942_; lean_object* v___x_4943_; 
v_fvarId_4942_ = lean_ctor_get(v_x_4936_, 0);
lean_inc(v_fvarId_4942_);
lean_dec_ref_known(v_x_4936_, 1);
v___x_4943_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4942_, v_a_4937_, v_a_4939_, v_a_4940_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v___x_4943_, 1);
v___x_4945_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4946_ = lean_unsigned_to_nat(0u);
v___x_4947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4945_, v_a_4944_, v___x_4946_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
return v___x_4947_;
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
v_a_4948_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4943_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4943_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4956_; lean_object* v___x_4957_; 
v_mvarId_4956_ = lean_ctor_get(v_x_4936_, 0);
lean_inc(v_mvarId_4956_);
lean_dec_ref_known(v_x_4936_, 1);
v___x_4957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4956_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4959_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4960_ = lean_unsigned_to_nat(0u);
v___x_4961_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4959_, v_a_4958_, v___x_4960_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
return v___x_4961_;
}
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
v_a_4962_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4957_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4957_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
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
case 3:
{
uint8_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
lean_dec_ref_known(v_x_4936_, 1);
v___x_4970_ = 0;
v___x_4971_ = lean_box(v___x_4970_);
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
return v___x_4972_;
}
case 4:
{
lean_object* v_declName_4973_; lean_object* v_us_4974_; lean_object* v___x_4975_; 
v_declName_4973_ = lean_ctor_get(v_x_4936_, 0);
lean_inc(v_declName_4973_);
v_us_4974_ = lean_ctor_get(v_x_4936_, 1);
lean_inc(v_us_4974_);
lean_dec_ref_known(v_x_4936_, 2);
v___x_4975_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4973_, v_us_4974_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v_fst_4977_; lean_object* v_snd_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v_fst_4977_ = lean_ctor_get(v_a_4976_, 0);
lean_inc(v_fst_4977_);
v_snd_4978_ = lean_ctor_get(v_a_4976_, 1);
lean_inc(v_snd_4978_);
lean_dec(v_a_4976_);
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4978_, v_fst_4977_, v___x_4979_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
return v___x_4980_;
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
v_a_4981_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4975_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4975_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
case 5:
{
lean_object* v_fn_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v_fn_4989_ = lean_ctor_get(v_x_4936_, 0);
lean_inc_ref(v_fn_4989_);
lean_dec_ref_known(v_x_4936_, 2);
v___x_4990_ = lean_unsigned_to_nat(1u);
v___x_4991_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4989_, v___x_4990_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
return v___x_4991_;
}
case 6:
{
lean_object* v_body_4992_; 
v_body_4992_ = lean_ctor_get(v_x_4936_, 2);
lean_inc_ref(v_body_4992_);
lean_dec_ref_known(v_x_4936_, 3);
v_x_4936_ = v_body_4992_;
goto _start;
}
case 7:
{
uint8_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
lean_dec_ref_known(v_x_4936_, 3);
v___x_4994_ = 0;
v___x_4995_ = lean_box(v___x_4994_);
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
return v___x_4996_;
}
case 8:
{
lean_object* v_body_4997_; 
v_body_4997_ = lean_ctor_get(v_x_4936_, 3);
lean_inc_ref(v_body_4997_);
lean_dec_ref_known(v_x_4936_, 4);
v_x_4936_ = v_body_4997_;
goto _start;
}
case 9:
{
uint8_t v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
lean_dec_ref_known(v_x_4936_, 1);
v___x_4999_ = 0;
v___x_5000_ = lean_box(v___x_4999_);
v___x_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5001_, 0, v___x_5000_);
return v___x_5001_;
}
case 10:
{
lean_object* v_expr_5002_; 
v_expr_5002_ = lean_ctor_get(v_x_4936_, 1);
lean_inc_ref(v_expr_5002_);
lean_dec_ref_known(v_x_4936_, 2);
v_x_4936_ = v_expr_5002_;
goto _start;
}
default: 
{
uint8_t v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_dec_ref(v_x_4936_);
v___x_5004_ = 2;
v___x_5005_ = lean_box(v___x_5004_);
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_5007_, lean_object* v_x_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
switch(lean_obj_tag(v_x_5007_))
{
case 4:
{
lean_object* v_declName_5014_; lean_object* v_us_5015_; lean_object* v___x_5016_; 
v_declName_5014_ = lean_ctor_get(v_x_5007_, 0);
lean_inc(v_declName_5014_);
v_us_5015_ = lean_ctor_get(v_x_5007_, 1);
lean_inc(v_us_5015_);
lean_dec_ref_known(v_x_5007_, 2);
v___x_5016_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5014_, v_us_5015_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v_fst_5018_; lean_object* v_snd_5019_; lean_object* v___x_5020_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v_fst_5018_ = lean_ctor_get(v_a_5017_, 0);
lean_inc(v_fst_5018_);
v_snd_5019_ = lean_ctor_get(v_a_5017_, 1);
lean_inc(v_snd_5019_);
lean_dec(v_a_5017_);
v___x_5020_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_5019_, v_fst_5018_, v_x_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_x_5008_);
return v___x_5020_;
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_x_5008_);
v_a_5021_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5016_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5016_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_5029_; lean_object* v___x_5030_; 
v_fvarId_5029_ = lean_ctor_get(v_x_5007_, 0);
lean_inc(v_fvarId_5029_);
lean_dec_ref_known(v_x_5007_, 1);
v___x_5030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5029_, v_a_5009_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v___x_5032_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5032_, v_a_5031_, v_x_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_x_5008_);
return v___x_5033_;
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_x_5008_);
v_a_5034_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5030_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5030_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5042_; lean_object* v___x_5043_; 
v_mvarId_5042_ = lean_ctor_get(v_x_5007_, 0);
lean_inc(v_mvarId_5042_);
lean_dec_ref_known(v_x_5007_, 1);
v___x_5043_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5042_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref_known(v___x_5043_, 1);
v___x_5045_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5046_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5045_, v_a_5044_, v_x_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_x_5008_);
return v___x_5046_;
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec(v_x_5008_);
v_a_5047_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5043_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5043_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
case 5:
{
lean_object* v_fn_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v_fn_5055_ = lean_ctor_get(v_x_5007_, 0);
lean_inc_ref(v_fn_5055_);
lean_dec_ref_known(v_x_5007_, 2);
v___x_5056_ = lean_unsigned_to_nat(1u);
v___x_5057_ = lean_nat_add(v_x_5008_, v___x_5056_);
lean_dec(v_x_5008_);
v_x_5007_ = v_fn_5055_;
v_x_5008_ = v___x_5057_;
goto _start;
}
case 10:
{
lean_object* v_expr_5059_; 
v_expr_5059_ = lean_ctor_get(v_x_5007_, 1);
lean_inc_ref(v_expr_5059_);
lean_dec_ref_known(v_x_5007_, 2);
v_x_5007_ = v_expr_5059_;
goto _start;
}
case 8:
{
lean_object* v_body_5061_; 
v_body_5061_ = lean_ctor_get(v_x_5007_, 3);
lean_inc_ref(v_body_5061_);
lean_dec_ref_known(v_x_5007_, 4);
v_x_5007_ = v_body_5061_;
goto _start;
}
case 6:
{
lean_object* v_body_5063_; lean_object* v_zero_5064_; uint8_t v_isZero_5065_; 
v_body_5063_ = lean_ctor_get(v_x_5007_, 2);
lean_inc_ref(v_body_5063_);
lean_dec_ref_known(v_x_5007_, 3);
v_zero_5064_ = lean_unsigned_to_nat(0u);
v_isZero_5065_ = lean_nat_dec_eq(v_x_5008_, v_zero_5064_);
if (v_isZero_5065_ == 1)
{
lean_object* v___x_5066_; 
lean_dec(v_x_5008_);
v___x_5066_ = l_Lean_Meta_isProofQuick(v_body_5063_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5066_;
}
else
{
lean_object* v_one_5067_; lean_object* v_n_5068_; 
v_one_5067_ = lean_unsigned_to_nat(1u);
v_n_5068_ = lean_nat_sub(v_x_5008_, v_one_5067_);
lean_dec(v_x_5008_);
v_x_5007_ = v_body_5063_;
v_x_5008_ = v_n_5068_;
goto _start;
}
}
default: 
{
uint8_t v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
lean_dec(v_x_5008_);
lean_dec_ref(v_x_5007_);
v___x_5070_ = 2;
v___x_5071_ = lean_box(v___x_5070_);
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
return v___x_5072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_5073_, lean_object* v_x_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_5073_, v_x_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5075_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Meta_isProofQuick(v_x_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v___x_5094_; 
lean_inc_ref(v_e_5088_);
v___x_5094_ = l_Lean_Meta_isProofQuick(v_e_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5121_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5121_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5121_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
uint8_t v___x_5099_; 
v___x_5099_ = lean_unbox(v_a_5095_);
lean_dec(v_a_5095_);
switch(v___x_5099_)
{
case 0:
{
uint8_t v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
lean_dec_ref(v_e_5088_);
v___x_5100_ = 0;
v___x_5101_ = lean_box(v___x_5100_);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5101_);
v___x_5103_ = v___x_5097_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
case 1:
{
uint8_t v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
lean_dec_ref(v_e_5088_);
v___x_5105_ = 1;
v___x_5106_ = lean_box(v___x_5105_);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5106_);
v___x_5108_ = v___x_5097_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
default: 
{
lean_object* v___x_5110_; 
lean_del_object(v___x_5097_);
lean_inc(v_a_5092_);
lean_inc_ref(v_a_5091_);
lean_inc(v_a_5090_);
lean_inc_ref(v_a_5089_);
v___x_5110_ = lean_infer_type(v_e_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = l_Lean_Meta_isProp(v_a_5111_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
return v___x_5112_;
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
v_a_5113_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5110_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5110_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec_ref(v_e_5088_);
v_a_5122_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5094_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5094_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_Meta_isProof(v_e_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_);
lean_dec(v_a_5134_);
lean_dec_ref(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_5137_, lean_object* v_x_5138_){
_start:
{
switch(lean_obj_tag(v_x_5137_))
{
case 3:
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = lean_unsigned_to_nat(0u);
v___x_5145_ = lean_nat_dec_eq(v_x_5138_, v___x_5144_);
lean_dec(v_x_5138_);
if (v___x_5145_ == 0)
{
goto v___jp_5140_;
}
else
{
uint8_t v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5146_ = 1;
v___x_5147_ = lean_box(v___x_5146_);
v___x_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5148_, 0, v___x_5147_);
return v___x_5148_;
}
}
case 7:
{
lean_object* v_body_5149_; lean_object* v_zero_5150_; uint8_t v_isZero_5151_; 
v_body_5149_ = lean_ctor_get(v_x_5137_, 2);
v_zero_5150_ = lean_unsigned_to_nat(0u);
v_isZero_5151_ = lean_nat_dec_eq(v_x_5138_, v_zero_5150_);
if (v_isZero_5151_ == 1)
{
uint8_t v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
lean_dec(v_x_5138_);
v___x_5152_ = 0;
v___x_5153_ = lean_box(v___x_5152_);
v___x_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5153_);
return v___x_5154_;
}
else
{
lean_object* v_one_5155_; lean_object* v_n_5156_; 
v_one_5155_ = lean_unsigned_to_nat(1u);
v_n_5156_ = lean_nat_sub(v_x_5138_, v_one_5155_);
lean_dec(v_x_5138_);
v_x_5137_ = v_body_5149_;
v_x_5138_ = v_n_5156_;
goto _start;
}
}
case 8:
{
lean_object* v_body_5158_; 
v_body_5158_ = lean_ctor_get(v_x_5137_, 3);
v_x_5137_ = v_body_5158_;
goto _start;
}
case 10:
{
lean_object* v_expr_5160_; 
v_expr_5160_ = lean_ctor_get(v_x_5137_, 1);
v_x_5137_ = v_expr_5160_;
goto _start;
}
default: 
{
lean_dec(v_x_5138_);
goto v___jp_5140_;
}
}
v___jp_5140_:
{
uint8_t v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5141_ = 2;
v___x_5142_ = lean_box(v___x_5141_);
v___x_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5142_);
return v___x_5143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_5162_, lean_object* v_x_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5162_, v_x_5163_);
lean_dec_ref(v_x_5162_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_5166_, lean_object* v_x_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v___x_5173_; 
v___x_5173_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5166_, v_x_5167_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_5174_, lean_object* v_x_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_5174_, v_x_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec_ref(v_x_5174_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_5182_, lean_object* v_x_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
switch(lean_obj_tag(v_x_5182_))
{
case 4:
{
lean_object* v_declName_5189_; lean_object* v_us_5190_; lean_object* v___x_5191_; 
v_declName_5189_ = lean_ctor_get(v_x_5182_, 0);
lean_inc(v_declName_5189_);
v_us_5190_ = lean_ctor_get(v_x_5182_, 1);
lean_inc(v_us_5190_);
lean_dec_ref_known(v_x_5182_, 2);
v___x_5191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5189_, v_us_5190_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v_fst_5193_; lean_object* v___x_5194_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
lean_inc(v_a_5192_);
lean_dec_ref_known(v___x_5191_, 1);
v_fst_5193_ = lean_ctor_get(v_a_5192_, 0);
lean_inc(v_fst_5193_);
lean_dec(v_a_5192_);
v___x_5194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5193_, v_x_5183_);
lean_dec(v_fst_5193_);
return v___x_5194_;
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v_x_5183_);
v_a_5195_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5191_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5191_);
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
case 1:
{
lean_object* v_fvarId_5203_; lean_object* v___x_5204_; 
v_fvarId_5203_ = lean_ctor_get(v_x_5182_, 0);
lean_inc(v_fvarId_5203_);
lean_dec_ref_known(v_x_5182_, 1);
v___x_5204_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5203_, v_a_5184_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v___x_5206_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref_known(v___x_5204_, 1);
v___x_5206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5205_, v_x_5183_);
lean_dec(v_a_5205_);
return v___x_5206_;
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
lean_dec(v_x_5183_);
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
case 2:
{
lean_object* v_mvarId_5215_; lean_object* v___x_5216_; 
v_mvarId_5215_ = lean_ctor_get(v_x_5182_, 0);
lean_inc(v_mvarId_5215_);
lean_dec_ref_known(v_x_5182_, 1);
v___x_5216_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5215_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5218_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
lean_inc(v_a_5217_);
lean_dec_ref_known(v___x_5216_, 1);
v___x_5218_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5217_, v_x_5183_);
lean_dec(v_a_5217_);
return v___x_5218_;
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
lean_dec(v_x_5183_);
v_a_5219_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5216_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5216_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
case 5:
{
lean_object* v_fn_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_fn_5227_ = lean_ctor_get(v_x_5182_, 0);
lean_inc_ref(v_fn_5227_);
lean_dec_ref_known(v_x_5182_, 2);
v___x_5228_ = lean_unsigned_to_nat(1u);
v___x_5229_ = lean_nat_add(v_x_5183_, v___x_5228_);
lean_dec(v_x_5183_);
v_x_5182_ = v_fn_5227_;
v_x_5183_ = v___x_5229_;
goto _start;
}
case 10:
{
lean_object* v_expr_5231_; 
v_expr_5231_ = lean_ctor_get(v_x_5182_, 1);
lean_inc_ref(v_expr_5231_);
lean_dec_ref_known(v_x_5182_, 2);
v_x_5182_ = v_expr_5231_;
goto _start;
}
case 8:
{
lean_object* v_body_5233_; 
v_body_5233_ = lean_ctor_get(v_x_5182_, 3);
lean_inc_ref(v_body_5233_);
lean_dec_ref_known(v_x_5182_, 4);
v_x_5182_ = v_body_5233_;
goto _start;
}
case 6:
{
lean_object* v_body_5235_; lean_object* v_zero_5236_; uint8_t v_isZero_5237_; 
v_body_5235_ = lean_ctor_get(v_x_5182_, 2);
lean_inc_ref(v_body_5235_);
lean_dec_ref_known(v_x_5182_, 3);
v_zero_5236_ = lean_unsigned_to_nat(0u);
v_isZero_5237_ = lean_nat_dec_eq(v_x_5183_, v_zero_5236_);
if (v_isZero_5237_ == 1)
{
uint8_t v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
lean_dec_ref(v_body_5235_);
lean_dec(v_x_5183_);
v___x_5238_ = 0;
v___x_5239_ = lean_box(v___x_5238_);
v___x_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5239_);
return v___x_5240_;
}
else
{
lean_object* v_one_5241_; lean_object* v_n_5242_; 
v_one_5241_ = lean_unsigned_to_nat(1u);
v_n_5242_ = lean_nat_sub(v_x_5183_, v_one_5241_);
lean_dec(v_x_5183_);
v_x_5182_ = v_body_5235_;
v_x_5183_ = v_n_5242_;
goto _start;
}
}
default: 
{
uint8_t v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
lean_dec(v_x_5183_);
lean_dec_ref(v_x_5182_);
v___x_5244_ = 2;
v___x_5245_ = lean_box(v___x_5244_);
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5245_);
return v___x_5246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_5247_, lean_object* v_x_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_5247_, v_x_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_);
lean_dec(v_a_5252_);
lean_dec_ref(v_a_5251_);
lean_dec(v_a_5250_);
lean_dec_ref(v_a_5249_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_){
_start:
{
switch(lean_obj_tag(v_x_5255_))
{
case 1:
{
lean_object* v_fvarId_5261_; lean_object* v___x_5262_; 
v_fvarId_5261_ = lean_ctor_get(v_x_5255_, 0);
lean_inc(v_fvarId_5261_);
lean_dec_ref_known(v_x_5255_, 1);
v___x_5262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5261_, v_a_5256_, v_a_5258_, v_a_5259_);
if (lean_obj_tag(v___x_5262_) == 0)
{
lean_object* v_a_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v_a_5263_ = lean_ctor_get(v___x_5262_, 0);
lean_inc(v_a_5263_);
lean_dec_ref_known(v___x_5262_, 1);
v___x_5264_ = lean_unsigned_to_nat(0u);
v___x_5265_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5263_, v___x_5264_);
lean_dec(v_a_5263_);
return v___x_5265_;
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
v_a_5266_ = lean_ctor_get(v___x_5262_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5262_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5262_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5274_; lean_object* v___x_5275_; 
v_mvarId_5274_ = lean_ctor_get(v_x_5255_, 0);
lean_inc(v_mvarId_5274_);
lean_dec_ref_known(v_x_5255_, 1);
v___x_5275_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5274_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
if (lean_obj_tag(v___x_5275_) == 0)
{
lean_object* v_a_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v_a_5276_ = lean_ctor_get(v___x_5275_, 0);
lean_inc(v_a_5276_);
lean_dec_ref_known(v___x_5275_, 1);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5276_, v___x_5277_);
lean_dec(v_a_5276_);
return v___x_5278_;
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5286_; 
v_a_5279_ = lean_ctor_get(v___x_5275_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5275_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5281_ = v___x_5275_;
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5275_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5284_; 
if (v_isShared_5282_ == 0)
{
v___x_5284_ = v___x_5281_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
case 3:
{
uint8_t v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec_ref_known(v_x_5255_, 1);
v___x_5287_ = 1;
v___x_5288_ = lean_box(v___x_5287_);
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
return v___x_5289_;
}
case 4:
{
lean_object* v_declName_5290_; lean_object* v_us_5291_; lean_object* v___x_5292_; 
v_declName_5290_ = lean_ctor_get(v_x_5255_, 0);
lean_inc(v_declName_5290_);
v_us_5291_ = lean_ctor_get(v_x_5255_, 1);
lean_inc(v_us_5291_);
lean_dec_ref_known(v_x_5255_, 2);
v___x_5292_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5290_, v_us_5291_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v_fst_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_a_5293_);
lean_dec_ref_known(v___x_5292_, 1);
v_fst_5294_ = lean_ctor_get(v_a_5293_, 0);
lean_inc(v_fst_5294_);
lean_dec(v_a_5293_);
v___x_5295_ = lean_unsigned_to_nat(0u);
v___x_5296_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5294_, v___x_5295_);
lean_dec(v_fst_5294_);
return v___x_5296_;
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
v_a_5297_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5292_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5292_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
case 5:
{
lean_object* v_fn_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v_fn_5305_ = lean_ctor_get(v_x_5255_, 0);
lean_inc_ref(v_fn_5305_);
lean_dec_ref_known(v_x_5255_, 2);
v___x_5306_ = lean_unsigned_to_nat(1u);
v___x_5307_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_5305_, v___x_5306_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
return v___x_5307_;
}
case 6:
{
uint8_t v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_dec_ref_known(v_x_5255_, 3);
v___x_5308_ = 0;
v___x_5309_ = lean_box(v___x_5308_);
v___x_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5309_);
return v___x_5310_;
}
case 7:
{
uint8_t v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
lean_dec_ref_known(v_x_5255_, 3);
v___x_5311_ = 1;
v___x_5312_ = lean_box(v___x_5311_);
v___x_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5312_);
return v___x_5313_;
}
case 8:
{
lean_object* v_body_5314_; 
v_body_5314_ = lean_ctor_get(v_x_5255_, 3);
lean_inc_ref(v_body_5314_);
lean_dec_ref_known(v_x_5255_, 4);
v_x_5255_ = v_body_5314_;
goto _start;
}
case 9:
{
uint8_t v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
lean_dec_ref_known(v_x_5255_, 1);
v___x_5316_ = 0;
v___x_5317_ = lean_box(v___x_5316_);
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
return v___x_5318_;
}
case 10:
{
lean_object* v_expr_5319_; 
v_expr_5319_ = lean_ctor_get(v_x_5255_, 1);
lean_inc_ref(v_expr_5319_);
lean_dec_ref_known(v_x_5255_, 2);
v_x_5255_ = v_expr_5319_;
goto _start;
}
default: 
{
uint8_t v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
lean_dec_ref(v_x_5255_);
v___x_5321_ = 2;
v___x_5322_ = lean_box(v___x_5321_);
v___x_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5323_, 0, v___x_5322_);
return v___x_5323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Lean_Meta_isTypeQuick(v_x_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v___x_5337_; 
lean_inc_ref(v_e_5331_);
v___x_5337_ = l_Lean_Meta_isTypeQuick(v_e_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5387_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5340_ = v___x_5337_;
v_isShared_5341_ = v_isSharedCheck_5387_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5337_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5387_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
uint8_t v___x_5342_; 
v___x_5342_ = lean_unbox(v_a_5338_);
lean_dec(v_a_5338_);
switch(v___x_5342_)
{
case 0:
{
uint8_t v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5346_; 
lean_dec_ref(v_e_5331_);
v___x_5343_ = 0;
v___x_5344_ = lean_box(v___x_5343_);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 0, v___x_5344_);
v___x_5346_ = v___x_5340_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5344_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
case 1:
{
uint8_t v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5351_; 
lean_dec_ref(v_e_5331_);
v___x_5348_ = 1;
v___x_5349_ = lean_box(v___x_5348_);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 0, v___x_5349_);
v___x_5351_ = v___x_5340_;
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
default: 
{
lean_object* v___x_5353_; 
lean_del_object(v___x_5340_);
lean_inc(v_a_5335_);
lean_inc_ref(v_a_5334_);
lean_inc(v_a_5333_);
lean_inc_ref(v_a_5332_);
v___x_5353_ = lean_infer_type(v_e_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5355_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref_known(v___x_5353_, 1);
v___x_5355_ = l_Lean_Meta_whnfD(v_a_5354_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5370_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5358_ = v___x_5355_;
v_isShared_5359_ = v_isSharedCheck_5370_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5355_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5370_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
if (lean_obj_tag(v_a_5356_) == 3)
{
uint8_t v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5363_; 
lean_dec_ref_known(v_a_5356_, 1);
v___x_5360_ = 1;
v___x_5361_ = lean_box(v___x_5360_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5361_);
v___x_5363_ = v___x_5358_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5361_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
else
{
uint8_t v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5368_; 
lean_dec(v_a_5356_);
v___x_5365_ = 0;
v___x_5366_ = lean_box(v___x_5365_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5366_);
v___x_5368_ = v___x_5358_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
v_a_5371_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5355_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5355_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
else
{
lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
v_a_5379_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5353_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5353_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_dec_ref(v_e_5331_);
v_a_5388_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5337_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5337_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l_Lean_Meta_isType(v_e_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
lean_dec(v_a_5398_);
lean_dec_ref(v_a_5397_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_5403_){
_start:
{
switch(lean_obj_tag(v_x_5403_))
{
case 7:
{
lean_object* v_body_5404_; 
v_body_5404_ = lean_ctor_get(v_x_5403_, 2);
v_x_5403_ = v_body_5404_;
goto _start;
}
case 3:
{
lean_object* v_u_5406_; lean_object* v___x_5407_; 
v_u_5406_ = lean_ctor_get(v_x_5403_, 0);
lean_inc(v_u_5406_);
v___x_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5407_, 0, v_u_5406_);
return v___x_5407_;
}
default: 
{
lean_object* v___x_5408_; 
v___x_5408_ = lean_box(0);
return v___x_5408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_5409_);
lean_dec_ref(v_x_5409_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5411_, lean_object* v_body_5412_, lean_object* v_x_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5411_, v_body_5412_, v_x_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5422_, lean_object* v_xs_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v_l_5430_; 
switch(lean_obj_tag(v_type_5422_))
{
case 3:
{
lean_object* v_u_5433_; 
lean_dec_ref(v_xs_5423_);
v_u_5433_ = lean_ctor_get(v_type_5422_, 0);
lean_inc(v_u_5433_);
lean_dec_ref_known(v_type_5422_, 1);
v_l_5430_ = v_u_5433_;
goto v___jp_5429_;
}
case 7:
{
lean_object* v_binderName_5434_; lean_object* v_binderType_5435_; lean_object* v_body_5436_; uint8_t v_binderInfo_5437_; lean_object* v___f_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v_binderName_5434_ = lean_ctor_get(v_type_5422_, 0);
lean_inc(v_binderName_5434_);
v_binderType_5435_ = lean_ctor_get(v_type_5422_, 1);
lean_inc_ref(v_binderType_5435_);
v_body_5436_ = lean_ctor_get(v_type_5422_, 2);
lean_inc_ref(v_body_5436_);
v_binderInfo_5437_ = lean_ctor_get_uint8(v_type_5422_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5422_, 3);
lean_inc_ref(v_xs_5423_);
v___f_5438_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5438_, 0, v_xs_5423_);
lean_closure_set(v___f_5438_, 1, v_body_5436_);
v___x_5439_ = lean_expr_instantiate_rev(v_binderType_5435_, v_xs_5423_);
lean_dec_ref(v_xs_5423_);
lean_dec_ref(v_binderType_5435_);
v___x_5440_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5434_, v_binderInfo_5437_, v___x_5439_, v___f_5438_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_);
return v___x_5440_;
}
default: 
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = lean_expr_instantiate_rev(v_type_5422_, v_xs_5423_);
lean_dec_ref(v_xs_5423_);
lean_dec_ref(v_type_5422_);
v___x_5442_ = l_Lean_Meta_whnfD(v___x_5441_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5454_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5454_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5454_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
switch(lean_obj_tag(v_a_5443_))
{
case 3:
{
lean_object* v_u_5447_; 
lean_del_object(v___x_5445_);
v_u_5447_ = lean_ctor_get(v_a_5443_, 0);
lean_inc(v_u_5447_);
lean_dec_ref_known(v_a_5443_, 1);
v_l_5430_ = v_u_5447_;
goto v___jp_5429_;
}
case 7:
{
lean_object* v___x_5448_; 
lean_del_object(v___x_5445_);
v___x_5448_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5422_ = v_a_5443_;
v_xs_5423_ = v___x_5448_;
goto _start;
}
default: 
{
lean_object* v___x_5450_; lean_object* v___x_5452_; 
lean_dec(v_a_5443_);
v___x_5450_ = lean_box(0);
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v___x_5450_);
v___x_5452_ = v___x_5445_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5450_);
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
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
v_a_5455_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5442_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5442_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
}
v___jp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5431_, 0, v_l_5430_);
v___x_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
return v___x_5432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5463_, lean_object* v_body_5464_, lean_object* v_x_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = lean_array_push(v_xs_5463_, v_x_5465_);
v___x_5472_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5464_, v___x_5471_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5473_, lean_object* v_xs_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5473_, v_xs_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5481_, lean_object* v_cache_5482_, lean_object* v_a_x3f_5483_){
_start:
{
lean_object* v___x_5485_; lean_object* v_mctx_5486_; lean_object* v_zetaDeltaFVarIds_5487_; lean_object* v_postponed_5488_; lean_object* v_diag_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5499_; 
v___x_5485_ = lean_st_ref_take(v_a_5481_);
v_mctx_5486_ = lean_ctor_get(v___x_5485_, 0);
v_zetaDeltaFVarIds_5487_ = lean_ctor_get(v___x_5485_, 2);
v_postponed_5488_ = lean_ctor_get(v___x_5485_, 3);
v_diag_5489_ = lean_ctor_get(v___x_5485_, 4);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5499_ == 0)
{
lean_object* v_unused_5500_; 
v_unused_5500_ = lean_ctor_get(v___x_5485_, 1);
lean_dec(v_unused_5500_);
v___x_5491_ = v___x_5485_;
v_isShared_5492_ = v_isSharedCheck_5499_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_diag_5489_);
lean_inc(v_postponed_5488_);
lean_inc(v_zetaDeltaFVarIds_5487_);
lean_inc(v_mctx_5486_);
lean_dec(v___x_5485_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5499_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5493_; lean_object* v___x_5495_; 
v___x_5493_ = lean_box(0);
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v_cache_5482_);
v___x_5495_ = v___x_5491_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_mctx_5486_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v_cache_5482_);
lean_ctor_set(v_reuseFailAlloc_5498_, 2, v_zetaDeltaFVarIds_5487_);
lean_ctor_set(v_reuseFailAlloc_5498_, 3, v_postponed_5488_);
lean_ctor_set(v_reuseFailAlloc_5498_, 4, v_diag_5489_);
v___x_5495_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5496_ = lean_st_ref_put(v_a_5481_, v___x_5495_);
v___x_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5493_);
return v___x_5497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5501_, lean_object* v_cache_5502_, lean_object* v_a_x3f_5503_, lean_object* v___y_5504_){
_start:
{
lean_object* v_res_5505_; 
v_res_5505_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5501_, v_cache_5502_, v_a_x3f_5503_);
lean_dec(v_a_x3f_5503_);
lean_dec(v_a_5501_);
return v_res_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_){
_start:
{
lean_object* v___x_5512_; 
v___x_5512_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5506_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v_cache_5515_; lean_object* v___x_5516_; 
v___x_5513_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5514_ = lean_st_ref_get(v_a_5508_);
v_cache_5515_ = lean_ctor_get(v___x_5514_, 1);
lean_inc_ref(v_cache_5515_);
lean_dec(v___x_5514_);
v___x_5516_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5506_, v___x_5513_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5533_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5519_ = v___x_5516_;
v_isShared_5520_ = v_isSharedCheck_5533_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5516_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5533_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
lean_inc(v_a_5517_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set_tag(v___x_5519_, 1);
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v___x_5523_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5508_, v_cache_5515_, v___x_5522_);
lean_dec_ref(v___x_5522_);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5530_ == 0)
{
lean_object* v_unused_5531_; 
v_unused_5531_ = lean_ctor_get(v___x_5523_, 0);
lean_dec(v_unused_5531_);
v___x_5525_ = v___x_5523_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_dec(v___x_5523_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
lean_ctor_set(v___x_5525_, 0, v_a_5517_);
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5517_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
}
else
{
lean_object* v_a_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
v_a_5534_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5516_, 1);
v___x_5535_ = lean_box(0);
v___x_5536_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5508_, v_cache_5515_, v___x_5535_);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v___x_5536_, 0);
lean_dec(v_unused_5544_);
v___x_5538_ = v___x_5536_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_dec(v___x_5536_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 1);
lean_ctor_set(v___x_5538_, 0, v_a_5534_);
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5534_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
else
{
lean_object* v___x_5545_; 
lean_dec_ref(v_type_5506_);
v___x_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5512_);
return v___x_5545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
lean_dec(v_a_5550_);
lean_dec_ref(v_a_5549_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5574_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5562_ = v___x_5559_;
v_isShared_5563_ = v_isSharedCheck_5574_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5559_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5574_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
if (lean_obj_tag(v_a_5560_) == 0)
{
uint8_t v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5564_ = 0;
v___x_5565_ = lean_box(v___x_5564_);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 0, v___x_5565_);
v___x_5567_ = v___x_5562_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5565_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
else
{
uint8_t v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5572_; 
lean_dec_ref_known(v_a_5560_, 1);
v___x_5569_ = 1;
v___x_5570_ = lean_box(v___x_5569_);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 0, v___x_5570_);
v___x_5572_ = v___x_5562_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
v_a_5575_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5559_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5559_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l_Lean_Meta_isTypeFormerType(v_type_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_);
lean_dec(v_a_5587_);
lean_dec_ref(v_a_5586_);
lean_dec(v_a_5585_);
lean_dec_ref(v_a_5584_);
return v_res_5589_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5590_, lean_object* v_x_5591_){
_start:
{
if (lean_obj_tag(v_x_5590_) == 0)
{
if (lean_obj_tag(v_x_5591_) == 0)
{
uint8_t v___x_5592_; 
v___x_5592_ = 1;
return v___x_5592_;
}
else
{
uint8_t v___x_5593_; 
v___x_5593_ = 0;
return v___x_5593_;
}
}
else
{
if (lean_obj_tag(v_x_5591_) == 0)
{
uint8_t v___x_5594_; 
v___x_5594_ = 0;
return v___x_5594_;
}
else
{
lean_object* v_val_5595_; lean_object* v_val_5596_; uint8_t v___x_5597_; 
v_val_5595_ = lean_ctor_get(v_x_5590_, 0);
v_val_5596_ = lean_ctor_get(v_x_5591_, 0);
v___x_5597_ = lean_level_eq(v_val_5595_, v_val_5596_);
return v___x_5597_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5598_, lean_object* v_x_5599_){
_start:
{
uint8_t v_res_5600_; lean_object* v_r_5601_; 
v_res_5600_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5598_, v_x_5599_);
lean_dec(v_x_5599_);
lean_dec(v_x_5598_);
v_r_5601_ = lean_box(v_res_5600_);
return v_r_5601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_){
_start:
{
lean_object* v___x_5610_; 
v___x_5610_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
if (lean_obj_tag(v___x_5610_) == 0)
{
lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5621_; 
v_a_5611_ = lean_ctor_get(v___x_5610_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5610_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5613_ = v___x_5610_;
v_isShared_5614_ = v_isSharedCheck_5621_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5610_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5621_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5615_; uint8_t v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5615_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5616_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5611_, v___x_5615_);
lean_dec(v_a_5611_);
v___x_5617_ = lean_box(v___x_5616_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 0, v___x_5617_);
v___x_5619_ = v___x_5613_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v___x_5617_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
v_a_5622_ = lean_ctor_get(v___x_5610_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5610_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5610_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5610_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_Lean_Meta_isPropFormerType(v_type_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v___x_5643_; 
lean_inc(v_a_5641_);
lean_inc_ref(v_a_5640_);
lean_inc(v_a_5639_);
lean_inc_ref(v_a_5638_);
v___x_5643_ = lean_infer_type(v_e_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v_a_5644_; lean_object* v___x_5645_; 
v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
lean_inc(v_a_5644_);
lean_dec_ref_known(v___x_5643_, 1);
v___x_5645_ = l_Lean_Meta_isTypeFormerType(v_a_5644_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
return v___x_5645_;
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
v_a_5646_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5643_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5643_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_a_5646_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Lean_Meta_isTypeFormer(v_e_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
lean_dec(v_a_5658_);
lean_dec_ref(v_a_5657_);
lean_dec(v_a_5656_);
lean_dec_ref(v_a_5655_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5661_, lean_object* v_maxFVars_x3f_5662_, lean_object* v_k_5663_, uint8_t v_cleanupAnnotations_5664_, uint8_t v_whnfType_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_){
_start:
{
lean_object* v___f_5671_; lean_object* v___x_5672_; 
v___f_5671_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5671_, 0, v_k_5663_);
v___x_5672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5661_, v_maxFVars_x3f_5662_, v___f_5671_, v_cleanupAnnotations_5664_, v_whnfType_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
if (lean_obj_tag(v___x_5672_) == 0)
{
lean_object* v_a_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5680_; 
v_a_5673_ = lean_ctor_get(v___x_5672_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5675_ = v___x_5672_;
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_a_5673_);
lean_dec(v___x_5672_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5678_; 
if (v_isShared_5676_ == 0)
{
v___x_5678_ = v___x_5675_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
v_a_5681_ = lean_ctor_get(v___x_5672_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5672_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5672_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5689_, lean_object* v_maxFVars_x3f_5690_, lean_object* v_k_5691_, lean_object* v_cleanupAnnotations_5692_, lean_object* v_whnfType_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5699_; uint8_t v_whnfType_boxed_5700_; lean_object* v_res_5701_; 
v_cleanupAnnotations_boxed_5699_ = lean_unbox(v_cleanupAnnotations_5692_);
v_whnfType_boxed_5700_ = lean_unbox(v_whnfType_5693_);
v_res_5701_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5689_, v_maxFVars_x3f_5690_, v_k_5691_, v_cleanupAnnotations_boxed_5699_, v_whnfType_boxed_5700_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_);
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5702_, lean_object* v_type_5703_, lean_object* v_maxFVars_x3f_5704_, lean_object* v_k_5705_, uint8_t v_cleanupAnnotations_5706_, uint8_t v_whnfType_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
lean_object* v___x_5713_; 
v___x_5713_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5703_, v_maxFVars_x3f_5704_, v_k_5705_, v_cleanupAnnotations_5706_, v_whnfType_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5714_, lean_object* v_type_5715_, lean_object* v_maxFVars_x3f_5716_, lean_object* v_k_5717_, lean_object* v_cleanupAnnotations_5718_, lean_object* v_whnfType_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5725_; uint8_t v_whnfType_boxed_5726_; lean_object* v_res_5727_; 
v_cleanupAnnotations_boxed_5725_ = lean_unbox(v_cleanupAnnotations_5718_);
v_whnfType_boxed_5726_ = lean_unbox(v_whnfType_5719_);
v_res_5727_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5714_, v_type_5715_, v_maxFVars_x3f_5716_, v_k_5717_, v_cleanupAnnotations_boxed_5725_, v_whnfType_boxed_5726_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
return v_res_5727_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5728_, lean_object* v_as_5729_, size_t v_i_5730_, size_t v_stop_5731_){
_start:
{
uint8_t v___x_5732_; 
v___x_5732_ = lean_usize_dec_eq(v_i_5730_, v_stop_5731_);
if (v___x_5732_ == 0)
{
lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5733_ = lean_array_uget_borrowed(v_as_5729_, v_i_5730_);
v___x_5734_ = lean_expr_eqv(v_a_5728_, v___x_5733_);
if (v___x_5734_ == 0)
{
size_t v___x_5735_; size_t v___x_5736_; 
v___x_5735_ = ((size_t)1ULL);
v___x_5736_ = lean_usize_add(v_i_5730_, v___x_5735_);
v_i_5730_ = v___x_5736_;
goto _start;
}
else
{
return v___x_5734_;
}
}
else
{
uint8_t v___x_5738_; 
v___x_5738_ = 0;
return v___x_5738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5739_, lean_object* v_as_5740_, lean_object* v_i_5741_, lean_object* v_stop_5742_){
_start:
{
size_t v_i_boxed_5743_; size_t v_stop_boxed_5744_; uint8_t v_res_5745_; lean_object* v_r_5746_; 
v_i_boxed_5743_ = lean_unbox_usize(v_i_5741_);
lean_dec(v_i_5741_);
v_stop_boxed_5744_ = lean_unbox_usize(v_stop_5742_);
lean_dec(v_stop_5742_);
v_res_5745_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5739_, v_as_5740_, v_i_boxed_5743_, v_stop_boxed_5744_);
lean_dec_ref(v_as_5740_);
lean_dec_ref(v_a_5739_);
v_r_5746_ = lean_box(v_res_5745_);
return v_r_5746_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; uint8_t v___x_5751_; 
v___x_5749_ = lean_unsigned_to_nat(0u);
v___x_5750_ = lean_array_get_size(v_as_5747_);
v___x_5751_ = lean_nat_dec_lt(v___x_5749_, v___x_5750_);
if (v___x_5751_ == 0)
{
return v___x_5751_;
}
else
{
size_t v___x_5752_; size_t v___x_5753_; uint8_t v___x_5754_; 
v___x_5752_ = ((size_t)0ULL);
v___x_5753_ = lean_usize_of_nat(v___x_5750_);
v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5748_, v_as_5747_, v___x_5752_, v___x_5753_);
return v___x_5754_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5755_, lean_object* v_a_5756_){
_start:
{
uint8_t v_res_5757_; lean_object* v_r_5758_; 
v_res_5757_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5755_, v_a_5756_);
lean_dec_ref(v_a_5756_);
lean_dec_ref(v_as_5755_);
v_r_5758_ = lean_box(v_res_5757_);
return v_r_5758_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5759_, lean_object* v_e_5760_){
_start:
{
uint8_t v___x_5761_; lean_object* v_d_5763_; lean_object* v_b_5764_; 
v___x_5761_ = l_Lean_Expr_hasFVar(v_e_5760_);
if (v___x_5761_ == 0)
{
lean_dec_ref(v_e_5760_);
return v___x_5761_;
}
else
{
switch(lean_obj_tag(v_e_5760_))
{
case 7:
{
lean_object* v_binderType_5767_; lean_object* v_body_5768_; 
v_binderType_5767_ = lean_ctor_get(v_e_5760_, 1);
lean_inc_ref(v_binderType_5767_);
v_body_5768_ = lean_ctor_get(v_e_5760_, 2);
lean_inc_ref(v_body_5768_);
lean_dec_ref_known(v_e_5760_, 3);
v_d_5763_ = v_binderType_5767_;
v_b_5764_ = v_body_5768_;
goto v___jp_5762_;
}
case 6:
{
lean_object* v_binderType_5769_; lean_object* v_body_5770_; 
v_binderType_5769_ = lean_ctor_get(v_e_5760_, 1);
lean_inc_ref(v_binderType_5769_);
v_body_5770_ = lean_ctor_get(v_e_5760_, 2);
lean_inc_ref(v_body_5770_);
lean_dec_ref_known(v_e_5760_, 3);
v_d_5763_ = v_binderType_5769_;
v_b_5764_ = v_body_5770_;
goto v___jp_5762_;
}
case 10:
{
lean_object* v_expr_5771_; 
v_expr_5771_ = lean_ctor_get(v_e_5760_, 1);
lean_inc_ref(v_expr_5771_);
lean_dec_ref_known(v_e_5760_, 2);
v_e_5760_ = v_expr_5771_;
goto _start;
}
case 8:
{
lean_object* v_type_5773_; lean_object* v_value_5774_; lean_object* v_body_5775_; uint8_t v___x_5776_; 
v_type_5773_ = lean_ctor_get(v_e_5760_, 1);
lean_inc_ref(v_type_5773_);
v_value_5774_ = lean_ctor_get(v_e_5760_, 2);
lean_inc_ref(v_value_5774_);
v_body_5775_ = lean_ctor_get(v_e_5760_, 3);
lean_inc_ref(v_body_5775_);
lean_dec_ref_known(v_e_5760_, 4);
v___x_5776_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5759_, v_type_5773_);
if (v___x_5776_ == 0)
{
uint8_t v___x_5777_; 
v___x_5777_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5759_, v_value_5774_);
if (v___x_5777_ == 0)
{
v_e_5760_ = v_body_5775_;
goto _start;
}
else
{
lean_dec_ref(v_body_5775_);
return v___x_5761_;
}
}
else
{
lean_dec_ref(v_body_5775_);
lean_dec_ref(v_value_5774_);
return v___x_5761_;
}
}
case 5:
{
lean_object* v_fn_5779_; lean_object* v_arg_5780_; uint8_t v___x_5781_; 
v_fn_5779_ = lean_ctor_get(v_e_5760_, 0);
lean_inc_ref(v_fn_5779_);
v_arg_5780_ = lean_ctor_get(v_e_5760_, 1);
lean_inc_ref(v_arg_5780_);
lean_dec_ref_known(v_e_5760_, 2);
v___x_5781_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5759_, v_fn_5779_);
if (v___x_5781_ == 0)
{
v_e_5760_ = v_arg_5780_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5780_);
return v___x_5761_;
}
}
case 11:
{
lean_object* v_struct_5783_; 
v_struct_5783_ = lean_ctor_get(v_e_5760_, 2);
lean_inc_ref(v_struct_5783_);
lean_dec_ref_known(v_e_5760_, 3);
v_e_5760_ = v_struct_5783_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5785_; lean_object* v___x_5786_; uint8_t v___x_5787_; 
v_fvarId_5785_ = lean_ctor_get(v_e_5760_, 0);
lean_inc(v_fvarId_5785_);
lean_dec_ref_known(v_e_5760_, 1);
v___x_5786_ = l_Lean_Expr_fvar___override(v_fvarId_5785_);
v___x_5787_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5759_, v___x_5786_);
lean_dec_ref(v___x_5786_);
return v___x_5787_;
}
default: 
{
uint8_t v___x_5788_; 
lean_dec_ref(v_e_5760_);
v___x_5788_ = 0;
return v___x_5788_;
}
}
}
v___jp_5762_:
{
uint8_t v___x_5765_; 
v___x_5765_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5759_, v_d_5763_);
if (v___x_5765_ == 0)
{
v_e_5760_ = v_b_5764_;
goto _start;
}
else
{
lean_dec_ref(v_b_5764_);
return v___x_5761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5789_, lean_object* v_e_5790_){
_start:
{
uint8_t v_res_5791_; lean_object* v_r_5792_; 
v_res_5791_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5789_, v_e_5790_);
lean_dec_ref(v_xs_5789_);
v_r_5792_ = lean_box(v_res_5791_);
return v_r_5792_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5795_ = l_Lean_stringToMessageData(v___x_5794_);
return v___x_5795_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5798_ = l_Lean_stringToMessageData(v___x_5797_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5799_, lean_object* v_type_5800_, lean_object* v_as_5801_, size_t v_sz_5802_, size_t v_i_5803_, lean_object* v_b_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v_a_5811_; uint8_t v___x_5815_; 
v___x_5815_ = lean_usize_dec_lt(v_i_5803_, v_sz_5802_);
if (v___x_5815_ == 0)
{
lean_object* v___x_5816_; 
lean_dec_ref(v_type_5800_);
v___x_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5816_, 0, v_b_5804_);
return v___x_5816_;
}
else
{
lean_object* v___x_5817_; lean_object* v_a_5818_; uint8_t v___x_5819_; 
v___x_5817_ = lean_box(0);
v_a_5818_ = lean_array_uget_borrowed(v_as_5801_, v_i_5803_);
lean_inc(v_a_5818_);
v___x_5819_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5799_, v_a_5818_);
if (v___x_5819_ == 0)
{
v_a_5811_ = v___x_5817_;
goto v___jp_5810_;
}
else
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5818_);
v___x_5821_ = l_Lean_MessageData_ofExpr(v_a_5818_);
v___x_5822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5820_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5822_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
lean_inc_ref(v_type_5800_);
v___x_5825_ = l_Lean_MessageData_ofExpr(v_type_5800_);
v___x_5826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5824_);
lean_ctor_set(v___x_5826_, 1, v___x_5825_);
v___x_5827_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5826_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
if (lean_obj_tag(v___x_5827_) == 0)
{
lean_dec_ref_known(v___x_5827_, 1);
v_a_5811_ = v___x_5817_;
goto v___jp_5810_;
}
else
{
lean_dec_ref(v_type_5800_);
return v___x_5827_;
}
}
}
v___jp_5810_:
{
size_t v___x_5812_; size_t v___x_5813_; 
v___x_5812_ = ((size_t)1ULL);
v___x_5813_ = lean_usize_add(v_i_5803_, v___x_5812_);
v_i_5803_ = v___x_5813_;
v_b_5804_ = v_a_5811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5828_, lean_object* v_type_5829_, lean_object* v_as_5830_, lean_object* v_sz_5831_, lean_object* v_i_5832_, lean_object* v_b_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
size_t v_sz_boxed_5839_; size_t v_i_boxed_5840_; lean_object* v_res_5841_; 
v_sz_boxed_5839_ = lean_unbox_usize(v_sz_5831_);
lean_dec(v_sz_5831_);
v_i_boxed_5840_ = lean_unbox_usize(v_i_5832_);
lean_dec(v_i_5832_);
v_res_5841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5828_, v_type_5829_, v_as_5830_, v_sz_boxed_5839_, v_i_boxed_5840_, v_b_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_);
lean_dec(v___y_5837_);
lean_dec_ref(v___y_5836_);
lean_dec(v___y_5835_);
lean_dec_ref(v___y_5834_);
lean_dec_ref(v_as_5830_);
lean_dec_ref(v_xs_5828_);
return v_res_5841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5842_, size_t v_i_5843_, lean_object* v_bs_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
uint8_t v___x_5850_; 
v___x_5850_ = lean_usize_dec_lt(v_i_5843_, v_sz_5842_);
if (v___x_5850_ == 0)
{
lean_object* v___x_5851_; 
v___x_5851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5851_, 0, v_bs_5844_);
return v___x_5851_;
}
else
{
lean_object* v_v_5852_; lean_object* v___x_5853_; lean_object* v_bs_x27_5854_; lean_object* v___x_5855_; 
v_v_5852_ = lean_array_uget(v_bs_5844_, v_i_5843_);
v___x_5853_ = lean_unsigned_to_nat(0u);
v_bs_x27_5854_ = lean_array_uset(v_bs_5844_, v_i_5843_, v___x_5853_);
lean_inc(v___y_5848_);
lean_inc_ref(v___y_5847_);
lean_inc(v___y_5846_);
lean_inc_ref(v___y_5845_);
v___x_5855_ = lean_infer_type(v_v_5852_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v_a_5856_; size_t v___x_5857_; size_t v___x_5858_; lean_object* v___x_5859_; 
v_a_5856_ = lean_ctor_get(v___x_5855_, 0);
lean_inc(v_a_5856_);
lean_dec_ref_known(v___x_5855_, 1);
v___x_5857_ = ((size_t)1ULL);
v___x_5858_ = lean_usize_add(v_i_5843_, v___x_5857_);
v___x_5859_ = lean_array_uset(v_bs_x27_5854_, v_i_5843_, v_a_5856_);
v_i_5843_ = v___x_5858_;
v_bs_5844_ = v___x_5859_;
goto _start;
}
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec_ref(v_bs_x27_5854_);
v_a_5861_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5855_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5855_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5869_, lean_object* v_i_5870_, lean_object* v_bs_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
size_t v_sz_boxed_5877_; size_t v_i_boxed_5878_; lean_object* v_res_5879_; 
v_sz_boxed_5877_ = lean_unbox_usize(v_sz_5869_);
lean_dec(v_sz_5869_);
v_i_boxed_5878_ = lean_unbox_usize(v_i_5870_);
lean_dec(v_i_5870_);
v_res_5879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5877_, v_i_boxed_5878_, v_bs_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
return v_res_5879_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5882_ = l_Lean_stringToMessageData(v___x_5881_);
return v___x_5882_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; 
v___x_5884_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5885_ = l_Lean_stringToMessageData(v___x_5884_);
return v___x_5885_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5887_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5888_ = l_Lean_stringToMessageData(v___x_5887_);
return v___x_5888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5889_, lean_object* v_n_5890_, lean_object* v_xs_5891_, lean_object* v_x_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
lean_object* v___x_5922_; uint8_t v___x_5923_; 
v___x_5922_ = lean_array_get_size(v_xs_5891_);
v___x_5923_ = lean_nat_dec_eq(v___x_5922_, v_n_5890_);
if (v___x_5923_ == 0)
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v_a_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5943_; 
lean_dec_ref(v_xs_5891_);
v___x_5924_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5925_ = l_Lean_MessageData_ofExpr(v_type_5889_);
v___x_5926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5924_);
lean_ctor_set(v___x_5926_, 1, v___x_5925_);
v___x_5927_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5926_);
lean_ctor_set(v___x_5928_, 1, v___x_5927_);
v___x_5929_ = l_Nat_reprFast(v_n_5890_);
v___x_5930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
v___x_5931_ = l_Lean_MessageData_ofFormat(v___x_5930_);
v___x_5932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5928_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5934_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
v_a_5936_ = lean_ctor_get(v___x_5935_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5935_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5938_ = v___x_5935_;
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_a_5936_);
lean_dec(v___x_5935_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5941_; 
if (v_isShared_5939_ == 0)
{
v___x_5941_ = v___x_5938_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5936_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
else
{
lean_dec(v_n_5890_);
goto v___jp_5898_;
}
v___jp_5898_:
{
size_t v_sz_5899_; size_t v___x_5900_; lean_object* v___x_5901_; 
v_sz_5899_ = lean_array_size(v_xs_5891_);
v___x_5900_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5891_);
v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5899_, v___x_5900_, v_xs_5891_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
if (lean_obj_tag(v___x_5901_) == 0)
{
lean_object* v_a_5902_; lean_object* v___x_5903_; size_t v_sz_5904_; lean_object* v___x_5905_; 
v_a_5902_ = lean_ctor_get(v___x_5901_, 0);
lean_inc(v_a_5902_);
lean_dec_ref_known(v___x_5901_, 1);
v___x_5903_ = lean_box(0);
v_sz_5904_ = lean_array_size(v_a_5902_);
v___x_5905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5891_, v_type_5889_, v_a_5902_, v_sz_5904_, v___x_5900_, v___x_5903_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
lean_dec_ref(v_xs_5891_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5912_ == 0)
{
lean_object* v_unused_5913_; 
v_unused_5913_ = lean_ctor_get(v___x_5905_, 0);
lean_dec(v_unused_5913_);
v___x_5907_ = v___x_5905_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_dec(v___x_5905_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
lean_ctor_set(v___x_5907_, 0, v_a_5902_);
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5902_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
else
{
lean_object* v_a_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5921_; 
lean_dec(v_a_5902_);
v_a_5914_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5921_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5916_ = v___x_5905_;
v_isShared_5917_ = v_isSharedCheck_5921_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_a_5914_);
lean_dec(v___x_5905_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5921_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v___x_5919_; 
if (v_isShared_5917_ == 0)
{
v___x_5919_ = v___x_5916_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_a_5914_);
v___x_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
return v___x_5919_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5891_);
lean_dec_ref(v_type_5889_);
return v___x_5901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5944_, lean_object* v_n_5945_, lean_object* v_xs_5946_, lean_object* v_x_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
lean_object* v_res_5953_; 
v_res_5953_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5944_, v_n_5945_, v_xs_5946_, v_x_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec_ref(v_x_5947_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5954_, lean_object* v_type_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
lean_object* v___f_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; lean_object* v___x_5964_; 
lean_inc(v_n_5954_);
lean_inc_ref(v_type_5955_);
v___f_5961_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5961_, 0, v_type_5955_);
lean_closure_set(v___f_5961_, 1, v_n_5954_);
v___x_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5962_, 0, v_n_5954_);
v___x_5963_ = 0;
v___x_5964_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5955_, v___x_5962_, v___f_5961_, v___x_5963_, v___x_5963_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5965_, lean_object* v_type_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
lean_object* v_res_5972_; 
v_res_5972_ = l_Lean_Meta_arrowDomainsN(v_n_5965_, v_type_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_);
lean_dec(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec_ref(v_a_5967_);
return v_res_5972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5973_, lean_object* v_e_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_){
_start:
{
lean_object* v___x_5980_; 
lean_inc(v_a_5978_);
lean_inc_ref(v_a_5977_);
lean_inc(v_a_5976_);
lean_inc_ref(v_a_5975_);
v___x_5980_ = lean_infer_type(v_e_5974_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_);
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v_a_5981_; lean_object* v___x_5982_; 
v_a_5981_ = lean_ctor_get(v___x_5980_, 0);
lean_inc(v_a_5981_);
lean_dec_ref_known(v___x_5980_, 1);
v___x_5982_ = l_Lean_Meta_arrowDomainsN(v_n_5973_, v_a_5981_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_);
return v___x_5982_;
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec(v_n_5973_);
v_a_5983_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5980_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5980_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5991_, lean_object* v_e_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l_Lean_Meta_inferArgumentTypesN(v_n_5991_, v_e_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_);
lean_dec(v_a_5996_);
lean_dec_ref(v_a_5995_);
lean_dec(v_a_5994_);
lean_dec_ref(v_a_5993_);
return v_res_5998_;
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
