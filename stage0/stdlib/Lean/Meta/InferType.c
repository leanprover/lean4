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
uint8_t l_Lean_Level_isAlwaysZero(lean_object*);
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
lean_dec_ref_known(v_e_280_, 2);
lean_dec_ref(v_fn_285_);
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
v___x_309_ = lean_unsigned_to_nat(1913u);
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
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_ctor_set(v___x_982_, 3, v___x_981_);
lean_ctor_set(v___x_982_, 4, v___x_980_);
lean_ctor_set(v___x_982_, 5, v___x_980_);
lean_ctor_set(v___x_982_, 6, v___x_980_);
lean_ctor_set(v___x_982_, 7, v___x_980_);
lean_ctor_set(v___x_982_, 8, v___x_980_);
lean_ctor_set(v___x_982_, 9, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_unsigned_to_nat(32u);
v___x_984_ = lean_mk_empty_array_with_capacity(v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_986_ = ((size_t)5ULL);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_unsigned_to_nat(32u);
v___x_989_ = lean_mk_empty_array_with_capacity(v___x_988_);
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_991_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_989_);
lean_ctor_set(v___x_991_, 2, v___x_987_);
lean_ctor_set(v___x_991_, 3, v___x_987_);
lean_ctor_set_usize(v___x_991_, 4, v___x_986_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = lean_box(1);
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
lean_ctor_set(v___x_995_, 2, v___x_992_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1017_, lean_object* v_declHint_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_env_1023_; uint8_t v___x_1024_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_st_ref_get(v___y_1019_);
v_env_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc_ref(v_env_1023_);
lean_dec(v___x_1022_);
v___x_1024_ = l_Lean_Name_isAnonymous(v_declHint_1018_);
if (v___x_1024_ == 0)
{
uint8_t v_isExporting_1025_; 
v_isExporting_1025_ = lean_ctor_get_uint8(v_env_1023_, sizeof(void*)*13);
if (v_isExporting_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v_env_1023_);
lean_dec(v_declHint_1018_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_msg_1017_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
lean_inc_ref(v_env_1023_);
v___x_1027_ = l_Lean_Environment_setExporting(v_env_1023_, v___x_1024_);
lean_inc(v_declHint_1018_);
lean_inc_ref(v___x_1027_);
v___x_1028_ = l_Lean_Environment_contains(v___x_1027_, v_declHint_1018_, v_isExporting_1025_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_env_1023_);
lean_dec(v_declHint_1018_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_msg_1017_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_c_1035_; lean_object* v___x_1036_; 
v___x_1030_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1032_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1027_);
v___x_1033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1030_);
lean_ctor_set(v___x_1033_, 2, v___x_1031_);
lean_ctor_set(v___x_1033_, 3, v___x_1032_);
lean_inc(v_declHint_1018_);
v___x_1034_ = l_Lean_MessageData_ofConstName(v_declHint_1018_, v___x_1024_);
v_c_1035_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1035_, 0, v___x_1033_);
lean_ctor_set(v_c_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1027_, v_declHint_1018_);
lean_dec_ref(v___x_1027_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_env_1023_);
lean_dec(v_declHint_1018_);
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_c_1035_);
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_MessageData_note(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_msg_1017_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1078_; 
v_val_1044_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1046_ = v___x_1036_;
v_isShared_1047_ = v_isSharedCheck_1078_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_val_1044_);
lean_dec(v___x_1036_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1078_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v_moduleNames_1049_; lean_object* v_mod_1050_; uint8_t v___x_1051_; 
v___x_1048_ = l_Lean_Environment_header(v_env_1023_);
lean_dec_ref(v_env_1023_);
v_moduleNames_1049_ = lean_ctor_get(v___x_1048_, 4);
lean_inc_ref(v_moduleNames_1049_);
lean_dec_ref(v___x_1048_);
v_mod_1050_ = lean_array_get(v___x_1021_, v_moduleNames_1049_, v_val_1044_);
lean_dec(v_val_1044_);
lean_dec_ref(v_moduleNames_1049_);
v___x_1051_ = l_Lean_isPrivateName(v_declHint_1018_);
lean_dec(v_declHint_1018_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_c_1035_);
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l_Lean_MessageData_ofName(v_mod_1050_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_MessageData_note(v___x_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_msg_1017_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1061_);
v___x_1063_ = v___x_1046_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_c_1035_);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofName(v_mod_1050_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_MessageData_note(v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_msg_1017_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1074_);
v___x_1076_ = v___x_1046_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1079_; 
lean_dec_ref(v_env_1023_);
lean_dec(v_declHint_1018_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_msg_1017_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1080_, lean_object* v_declHint_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1080_, v_declHint_1081_, v___y_1082_);
lean_dec(v___y_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1085_, lean_object* v_declHint_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
v___x_1092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1085_, v_declHint_1086_, v___y_1090_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1097_ = l_Lean_unknownIdentifierMessageTag;
v___x_1098_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1103_, lean_object* v_declHint_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1103_, v_declHint_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1111_, lean_object* v_msg_1112_, lean_object* v_declHint_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1112_, v_declHint_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1111_, v_a_1120_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1122_, lean_object* v_msg_1123_, lean_object* v_declHint_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1122_, v_msg_1123_, v_declHint_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v_ref_1122_);
return v_res_1130_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1137_, lean_object* v_constName_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1144_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1145_ = 0;
lean_inc(v_constName_1138_);
v___x_1146_ = l_Lean_MessageData_ofConstName(v_constName_1138_, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1144_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1137_, v___x_1149_, v_constName_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1151_, lean_object* v_constName_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1151_, v_constName_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v_ref_1151_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_ref_1165_; lean_object* v___x_1166_; 
v_ref_1165_ = lean_ctor_get(v___y_1162_, 2);
v___x_1166_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1165_, v_constName_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_env_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = lean_st_ref_get(v___y_1178_);
v_env_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_ref(v_env_1181_);
lean_dec(v___x_1180_);
v___x_1182_ = 0;
lean_inc(v_constName_1174_);
v___x_1183_ = l_Lean_Environment_findConstVal_x3f(v_env_1181_, v_constName_1174_, v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_constName_1174_);
v_val_1185_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_val_1185_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 0);
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_val_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1200_, lean_object* v_us_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; 
lean_inc(v_c_1200_);
v___x_1207_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1200_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v_levelParams_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v_levelParams_1209_ = lean_ctor_get(v_a_1208_, 1);
v___x_1210_ = l_List_lengthTR___redArg(v_levelParams_1209_);
v___x_1211_ = l_List_lengthTR___redArg(v_us_1201_);
v___x_1212_ = lean_nat_dec_eq(v___x_1210_, v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1210_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v_a_1208_);
v___x_1213_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1200_, v_us_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; 
lean_dec(v_c_1200_);
v___x_1214_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1208_, v_us_1201_, v_a_1205_);
return v___x_1214_;
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_us_1201_);
lean_dec(v_c_1200_);
v_a_1215_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1207_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1207_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1223_, lean_object* v_us_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1223_, v_us_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1231_, lean_object* v_constName_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_constName_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1239_, v_constName_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1247_, lean_object* v_ref_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1248_, v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_ref_1257_, lean_object* v_constName_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1256_, v_ref_1257_, v_constName_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1257_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1265_, lean_object* v_ref_1266_, lean_object* v_msg_1267_, lean_object* v_declHint_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1266_, v_msg_1267_, v_declHint_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_msg_1277_, lean_object* v_declHint_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1275_, v_ref_1276_, v_msg_1277_, v_declHint_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v_ref_1276_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1285_, lean_object* v_declHint_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1285_, v_declHint_1286_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1293_, lean_object* v_declHint_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1293_, v_declHint_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1301_, lean_object* v_ref_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1302_, v_msg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1310_, lean_object* v_ref_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1310_, v_ref_1311_, v_msg_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v_ref_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply(lean_object* v_00_u03c3_1319_, lean_object* v_u_1320_){
_start:
{
lean_object* v_paramNames_1321_; lean_object* v_lvls_1322_; uint8_t v___x_1323_; 
v_paramNames_1321_ = lean_ctor_get(v_00_u03c3_1319_, 0);
lean_inc(v_paramNames_1321_);
v_lvls_1322_ = lean_ctor_get(v_00_u03c3_1319_, 1);
lean_inc(v_lvls_1322_);
lean_dec_ref(v_00_u03c3_1319_);
v___x_1323_ = l_List_isEmpty___redArg(v_paramNames_1321_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Level_instantiateParams(v_u_1320_, v_paramNames_1321_, v_lvls_1322_);
return v___x_1324_;
}
else
{
lean_dec(v_lvls_1322_);
lean_dec(v_paramNames_1321_);
return v_u_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_applyList(lean_object* v_00_u03c3_1325_, lean_object* v_us_1326_){
_start:
{
lean_object* v_paramNames_1327_; uint8_t v___x_1328_; 
v_paramNames_1327_ = lean_ctor_get(v_00_u03c3_1325_, 0);
v___x_1328_ = l_List_isEmpty___redArg(v_paramNames_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply), 2, 1);
lean_closure_set(v___x_1329_, 0, v_00_u03c3_1325_);
v___x_1330_ = lean_box(0);
v___x_1331_ = l_List_mapTR_loop___redArg(v___x_1329_, v_us_1326_, v___x_1330_);
return v___x_1331_;
}
else
{
lean_dec_ref(v_00_u03c3_1325_);
return v_us_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(lean_object* v_c_1332_, lean_object* v_us_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; 
lean_inc(v_c_1332_);
v___x_1339_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1332_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1355_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_levelParams_1344_; lean_object* v_type_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_levelParams_1344_ = lean_ctor_get(v_a_1340_, 1);
lean_inc(v_levelParams_1344_);
v_type_1345_ = lean_ctor_get(v_a_1340_, 2);
lean_inc_ref(v_type_1345_);
lean_dec(v_a_1340_);
v___x_1346_ = l_List_lengthTR___redArg(v_levelParams_1344_);
v___x_1347_ = l_List_lengthTR___redArg(v_us_1333_);
v___x_1348_ = lean_nat_dec_eq(v___x_1346_, v___x_1347_);
lean_dec(v___x_1347_);
lean_dec(v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref(v_type_1345_);
lean_dec(v_levelParams_1344_);
lean_del_object(v___x_1342_);
v___x_1349_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1332_, v_us_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec(v_c_1332_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_levelParams_1344_);
lean_ctor_set(v___x_1350_, 1, v_us_1333_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_type_1345_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1351_);
v___x_1353_ = v___x_1342_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_us_1333_);
lean_dec(v_c_1332_);
v_a_1356_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1339_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1339_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy___boxed(lean_object* v_c_1364_, lean_object* v_us_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_c_1364_, v_us_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1378_, lean_object* v_idx_1379_, lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v_00_u03b1_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1389_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1390_ = l_Lean_mkProj(v_structName_1378_, v_idx_1379_, v_e_1380_);
v___x_1391_ = l_Lean_indentExpr(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1389_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = l_Lean_indentExpr(v_a_1381_);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1396_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1398_, lean_object* v_idx_1399_, lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v_00_u03b1_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1398_, v_idx_1399_, v_e_1400_, v_a_1401_, v_00_u03b1_1402_, v_x_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v_env_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_st_ref_get(v___y_1414_);
v_env_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc_ref(v_env_1417_);
lean_dec(v___x_1416_);
v___x_1418_ = 0;
lean_inc(v_constName_1410_);
v___x_1419_ = l_Lean_Environment_find_x3f(v_env_1417_, v_constName_1410_, v___x_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_constName_1410_);
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1419_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_dec(v___x_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 0);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_val_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1436_, lean_object* v_structName_1437_, lean_object* v_e_1438_, lean_object* v_idx_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_a_1449_; uint8_t v___x_1453_; 
v___x_1453_ = lean_nat_dec_lt(v_a_1441_, v_upperBound_1436_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_idx_1439_);
lean_dec_ref(v_e_1438_);
lean_dec(v_structName_1437_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1442_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
v___x_1455_ = lean_whnf(v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
if (lean_obj_tag(v_a_1456_) == 7)
{
lean_object* v_body_1457_; uint8_t v___x_1458_; 
v_body_1457_ = lean_ctor_get(v_a_1456_, 2);
lean_inc_ref(v_body_1457_);
lean_dec_ref_known(v_a_1456_, 3);
v___x_1458_ = l_Lean_Expr_hasLooseBVars(v_body_1457_);
if (v___x_1458_ == 0)
{
v_a_1449_ = v_body_1457_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc_ref(v_e_1438_);
lean_inc(v_a_1441_);
lean_inc(v_structName_1437_);
v___x_1459_ = l_Lean_mkProj(v_structName_1437_, v_a_1441_, v_e_1438_);
v___x_1460_ = lean_expr_instantiate1(v_body_1457_, v___x_1459_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_body_1457_);
v_a_1449_ = v___x_1460_;
goto v___jp_1448_;
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1438_);
lean_inc(v_idx_1439_);
lean_inc(v_structName_1437_);
v___x_1462_ = l_Lean_mkProj(v_structName_1437_, v_idx_1439_, v_e_1438_);
v___x_1463_ = l_Lean_indentExpr(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1461_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
lean_inc_ref(v_a_1440_);
v___x_1467_ = l_Lean_indentExpr(v_a_1440_);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1468_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v_a_1449_ = v_a_1456_;
goto v___jp_1448_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1456_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_idx_1439_);
lean_dec_ref(v_e_1438_);
lean_dec(v_structName_1437_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_idx_1439_);
lean_dec_ref(v_e_1438_);
lean_dec(v_structName_1437_);
return v___x_1455_;
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_a_1441_, v___x_1450_);
lean_dec(v_a_1441_);
v_a_1441_ = v___x_1451_;
v_b_1442_ = v_a_1449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1478_, lean_object* v_structName_1479_, lean_object* v_e_1480_, lean_object* v_idx_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1478_, v_structName_1479_, v_e_1480_, v_idx_1481_, v_a_1482_, v_a_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_upperBound_1478_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1491_, lean_object* v_structName_1492_, lean_object* v_e_1493_, lean_object* v_idx_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_a_1504_; uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_lt(v_a_1496_, v_upperBound_1491_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_idx_1494_);
lean_dec_ref(v_e_1493_);
lean_dec(v_structName_1492_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_b_1497_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc_ref(v___y_1498_);
v___x_1510_ = lean_whnf(v_b_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
if (lean_obj_tag(v_a_1511_) == 7)
{
lean_object* v_body_1512_; uint8_t v___x_1513_; 
v_body_1512_ = lean_ctor_get(v_a_1511_, 2);
lean_inc_ref(v_body_1512_);
lean_dec_ref_known(v_a_1511_, 3);
v___x_1513_ = l_Lean_Expr_hasLooseBVars(v_body_1512_);
if (v___x_1513_ == 0)
{
v_a_1504_ = v_body_1512_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_inc_ref(v_e_1493_);
lean_inc(v_a_1496_);
lean_inc(v_structName_1492_);
v___x_1514_ = l_Lean_mkProj(v_structName_1492_, v_a_1496_, v_e_1493_);
v___x_1515_ = lean_expr_instantiate1(v_body_1512_, v___x_1514_);
lean_dec_ref(v___x_1514_);
lean_dec_ref(v_body_1512_);
v_a_1504_ = v___x_1515_;
goto v___jp_1503_;
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1516_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1493_);
lean_inc(v_idx_1494_);
lean_inc(v_structName_1492_);
v___x_1517_ = l_Lean_mkProj(v_structName_1492_, v_idx_1494_, v_e_1493_);
v___x_1518_ = l_Lean_indentExpr(v___x_1517_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1516_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
lean_inc_ref(v_a_1495_);
v___x_1522_ = l_Lean_indentExpr(v_a_1495_);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1523_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_dec_ref_known(v___x_1524_, 1);
v_a_1504_ = v_a_1511_;
goto v___jp_1503_;
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1511_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_idx_1494_);
lean_dec_ref(v_e_1493_);
lean_dec(v_structName_1492_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
else
{
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_idx_1494_);
lean_dec_ref(v_e_1493_);
lean_dec(v_structName_1492_);
return v___x_1510_;
}
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_add(v_a_1496_, v___x_1505_);
lean_dec(v_a_1496_);
v___x_1507_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1491_, v_structName_1492_, v_e_1493_, v_idx_1494_, v_a_1495_, v___x_1506_, v_a_1504_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1533_, lean_object* v_structName_1534_, lean_object* v_e_1535_, lean_object* v_idx_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1533_, v_structName_1534_, v_e_1535_, v_idx_1536_, v_a_1537_, v_a_1538_, v_b_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v_upperBound_1533_);
return v_res_1545_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1546_; lean_object* v_dummy_1547_; 
v___x_1546_ = lean_box(0);
v_dummy_1547_ = l_Lean_Expr_sort___override(v___x_1546_);
return v_dummy_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1548_, lean_object* v_idx_1549_, lean_object* v_e_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; 
lean_inc(v_a_1554_);
lean_inc_ref(v_a_1553_);
lean_inc(v_a_1552_);
lean_inc_ref(v_a_1551_);
lean_inc_ref(v_e_1550_);
v___x_1556_ = lean_infer_type(v_e_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
lean_inc(v_a_1554_);
lean_inc_ref(v_a_1553_);
lean_inc(v_a_1552_);
lean_inc_ref(v_a_1551_);
v___x_1558_ = lean_whnf(v_a_1557_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = l_Lean_Expr_getAppFn(v_a_1559_);
if (lean_obj_tag(v___x_1560_) == 4)
{
lean_object* v_declName_1561_; lean_object* v_us_1562_; lean_object* v___x_1563_; lean_object* v_env_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v_declName_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_declName_1561_);
v_us_1562_ = lean_ctor_get(v___x_1560_, 1);
lean_inc(v_us_1562_);
lean_dec_ref_known(v___x_1560_, 2);
v___x_1563_ = lean_st_ref_get(v_a_1554_);
v_env_1567_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_env_1567_);
lean_dec(v___x_1563_);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_Environment_find_x3f(v_env_1567_, v_declName_1561_, v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_us_1562_);
v___x_1570_ = lean_box(0);
v___x_1571_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1570_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; 
v_val_1572_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___x_1569_, 1);
if (lean_obj_tag(v_val_1572_) == 5)
{
lean_object* v_val_1573_; lean_object* v_ctors_1574_; 
v_val_1573_ = lean_ctor_get(v_val_1572_, 0);
lean_inc_ref(v_val_1573_);
lean_dec_ref_known(v_val_1572_, 1);
v_ctors_1574_ = lean_ctor_get(v_val_1573_, 4);
lean_inc(v_ctors_1574_);
if (lean_obj_tag(v_ctors_1574_) == 1)
{
lean_object* v_tail_1575_; 
v_tail_1575_ = lean_ctor_get(v_ctors_1574_, 1);
if (lean_obj_tag(v_tail_1575_) == 0)
{
lean_object* v_toConstantVal_1576_; lean_object* v_numParams_1577_; lean_object* v_numIndices_1578_; lean_object* v_head_1579_; lean_object* v___x_1580_; 
v_toConstantVal_1576_ = lean_ctor_get(v_val_1573_, 0);
lean_inc_ref(v_toConstantVal_1576_);
v_numParams_1577_ = lean_ctor_get(v_val_1573_, 1);
lean_inc(v_numParams_1577_);
v_numIndices_1578_ = lean_ctor_get(v_val_1573_, 2);
lean_inc(v_numIndices_1578_);
lean_dec_ref(v_val_1573_);
v_head_1579_ = lean_ctor_get(v_ctors_1574_, 0);
lean_inc(v_head_1579_);
lean_dec_ref_known(v_ctors_1574_, 2);
v___x_1580_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1579_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 6)
{
lean_object* v_val_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v_name_1622_; uint8_t v___x_1623_; 
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc_ref(v_val_1582_);
lean_dec_ref_known(v_a_1581_, 1);
v_name_1622_ = lean_ctor_get(v_toConstantVal_1576_, 0);
lean_inc(v_name_1622_);
lean_dec_ref(v_toConstantVal_1576_);
v___x_1623_ = lean_name_eq(v_name_1622_, v_structName_1548_);
lean_dec(v_name_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_val_1582_);
lean_dec(v_numIndices_1578_);
lean_dec(v_numParams_1577_);
lean_dec(v_us_1562_);
v___x_1624_ = lean_box(0);
v___x_1625_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1624_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
v___y_1584_ = v_a_1551_;
v___y_1585_ = v_a_1552_;
v___y_1586_ = v_a_1553_;
v___y_1587_ = v_a_1554_;
goto v___jp_1583_;
}
v___jp_1583_:
{
lean_object* v_dummy_1588_; lean_object* v_nargs_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v_dummy_1588_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1589_ = l_Lean_Expr_getAppNumArgs(v_a_1559_);
lean_inc(v_nargs_1589_);
v___x_1590_ = lean_mk_array(v_nargs_1589_, v_dummy_1588_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_sub(v_nargs_1589_, v___x_1591_);
lean_dec(v_nargs_1589_);
lean_inc(v_a_1559_);
v___x_1593_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1559_, v___x_1590_, v___x_1592_);
v___x_1594_ = lean_nat_add(v_numParams_1577_, v_numIndices_1578_);
lean_dec(v_numIndices_1578_);
v___x_1595_ = lean_array_get_size(v___x_1593_);
v___x_1596_ = lean_nat_dec_eq(v___x_1594_, v___x_1595_);
lean_dec(v___x_1594_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref(v___x_1593_);
lean_dec_ref(v_val_1582_);
lean_dec(v_numParams_1577_);
lean_dec(v_us_1562_);
v___x_1597_ = lean_box(0);
v___x_1598_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1597_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1598_;
}
else
{
lean_object* v_toConstantVal_1599_; lean_object* v_name_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_toConstantVal_1599_ = lean_ctor_get(v_val_1582_, 0);
lean_inc_ref(v_toConstantVal_1599_);
lean_dec_ref(v_val_1582_);
v_name_1600_ = lean_ctor_get(v_toConstantVal_1599_, 0);
lean_inc(v_name_1600_);
lean_dec_ref(v_toConstantVal_1599_);
v___x_1601_ = l_Lean_mkConst(v_name_1600_, v_us_1562_);
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = l_Array_toSubarray___redArg(v___x_1593_, v___x_1602_, v_numParams_1577_);
v___x_1604_ = l_Subarray_copy___redArg(v___x_1603_);
v___x_1605_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1601_, v___x_1604_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec_ref(v___x_1604_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
lean_inc(v_a_1559_);
lean_inc_ref(v_e_1550_);
lean_inc(v_structName_1548_);
lean_inc(v_idx_1549_);
v___x_1607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1549_, v_structName_1548_, v_e_1550_, v_idx_1549_, v_a_1559_, v___x_1602_, v_a_1606_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
v___x_1609_ = lean_whnf(v_a_1608_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1621_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1621_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1621_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
if (lean_obj_tag(v_a_1610_) == 7)
{
lean_object* v_binderType_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec(v_a_1559_);
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
v_binderType_1614_ = lean_ctor_get(v_a_1610_, 1);
lean_inc_ref(v_binderType_1614_);
lean_dec_ref_known(v_a_1610_, 3);
v___x_1615_ = lean_expr_consume_type_annotations(v_binderType_1614_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_del_object(v___x_1612_);
lean_dec(v_a_1610_);
v___x_1619_ = lean_box(0);
v___x_1620_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1619_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1620_;
}
}
}
else
{
lean_dec(v_a_1559_);
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
return v___x_1609_;
}
}
else
{
lean_dec(v_a_1559_);
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
return v___x_1607_;
}
}
else
{
lean_dec(v_a_1559_);
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
return v___x_1605_;
}
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec(v_a_1581_);
lean_dec(v_numIndices_1578_);
lean_dec(v_numParams_1577_);
lean_dec_ref(v_toConstantVal_1576_);
lean_dec(v_us_1562_);
v___x_1634_ = lean_box(0);
v___x_1635_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1634_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_numIndices_1578_);
lean_dec(v_numParams_1577_);
lean_dec_ref(v_toConstantVal_1576_);
lean_dec(v_us_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
v_a_1636_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1580_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1580_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1574_, 2);
lean_dec_ref(v_val_1573_);
lean_dec(v_us_1562_);
goto v___jp_1564_;
}
}
else
{
lean_dec(v_ctors_1574_);
lean_dec_ref(v_val_1573_);
lean_dec(v_us_1562_);
goto v___jp_1564_;
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_val_1572_);
lean_dec(v_us_1562_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1644_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1645_;
}
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1565_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1566_;
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v___x_1560_);
v___x_1646_ = lean_box(0);
v___x_1647_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1548_, v_idx_1549_, v_e_1550_, v_a_1559_, lean_box(0), v___x_1646_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1647_;
}
}
else
{
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
return v___x_1558_;
}
}
else
{
lean_dec_ref(v_e_1550_);
lean_dec(v_idx_1549_);
lean_dec(v_structName_1548_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1648_, lean_object* v_idx_1649_, lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1648_, v_idx_1649_, v_e_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1657_, lean_object* v_structName_1658_, lean_object* v_e_1659_, lean_object* v_idx_1660_, lean_object* v_a_1661_, lean_object* v_inst_1662_, lean_object* v_R_1663_, lean_object* v_a_1664_, lean_object* v_b_1665_, lean_object* v_c_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1657_, v_structName_1658_, v_e_1659_, v_idx_1660_, v_a_1661_, v_a_1664_, v_b_1665_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1673_, lean_object* v_structName_1674_, lean_object* v_e_1675_, lean_object* v_idx_1676_, lean_object* v_a_1677_, lean_object* v_inst_1678_, lean_object* v_R_1679_, lean_object* v_a_1680_, lean_object* v_b_1681_, lean_object* v_c_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1673_, v_structName_1674_, v_e_1675_, v_idx_1676_, v_a_1677_, v_inst_1678_, v_R_1679_, v_a_1680_, v_b_1681_, v_c_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_upperBound_1673_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1689_, lean_object* v_structName_1690_, lean_object* v_e_1691_, lean_object* v_idx_1692_, lean_object* v_a_1693_, lean_object* v_inst_1694_, lean_object* v_R_1695_, lean_object* v_a_1696_, lean_object* v_b_1697_, lean_object* v_c_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1689_, v_structName_1690_, v_e_1691_, v_idx_1692_, v_a_1693_, v_a_1696_, v_b_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1705_, lean_object* v_structName_1706_, lean_object* v_e_1707_, lean_object* v_idx_1708_, lean_object* v_a_1709_, lean_object* v_inst_1710_, lean_object* v_R_1711_, lean_object* v_a_1712_, lean_object* v_b_1713_, lean_object* v_c_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1705_, v_structName_1706_, v_e_1707_, v_idx_1708_, v_a_1709_, v_inst_1710_, v_R_1711_, v_a_1712_, v_b_1713_, v_c_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_upperBound_1705_);
return v_res_1720_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1731_ = l_Lean_indentExpr(v_type_1724_);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1732_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1741_, lean_object* v_type_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1749_, lean_object* v_type_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1749_, v_type_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v_ks_1761_; lean_object* v_vs_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1786_; 
v_ks_1761_ = lean_ctor_get(v_x_1757_, 0);
v_vs_1762_ = lean_ctor_get(v_x_1757_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1757_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1764_ = v_x_1757_;
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_vs_1762_);
lean_inc(v_ks_1761_);
lean_dec(v_x_1757_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1786_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_array_get_size(v_ks_1761_);
v___x_1767_ = lean_nat_dec_lt(v_x_1758_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec(v_x_1758_);
v___x_1768_ = lean_array_push(v_ks_1761_, v_x_1759_);
v___x_1769_ = lean_array_push(v_vs_1762_, v_x_1760_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1769_);
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1771_ = v___x_1764_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v_k_x27_1773_; uint8_t v___x_1774_; 
v_k_x27_1773_ = lean_array_fget_borrowed(v_ks_1761_, v_x_1758_);
v___x_1774_ = l_Lean_instBEqMVarId_beq(v_x_1759_, v_k_x27_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1776_; 
if (v_isShared_1765_ == 0)
{
v___x_1776_ = v___x_1764_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_ks_1761_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_vs_1762_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_x_1758_, v___x_1777_);
lean_dec(v_x_1758_);
v_x_1757_ = v___x_1776_;
v_x_1758_ = v___x_1778_;
goto _start;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = lean_array_fset(v_ks_1761_, v_x_1758_, v_x_1759_);
v___x_1782_ = lean_array_fset(v_vs_1762_, v_x_1758_, v_x_1760_);
lean_dec(v_x_1758_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1782_);
lean_ctor_set(v___x_1764_, 0, v___x_1781_);
v___x_1784_ = v___x_1764_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1787_, lean_object* v_k_1788_, lean_object* v_v_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1787_, v___x_1790_, v_k_1788_, v_v_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1793_, size_t v_x_1794_, size_t v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
lean_object* v_es_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v_j_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_es_1798_ = lean_ctor_get(v_x_1793_, 0);
v___x_1799_ = ((size_t)31ULL);
v___x_1800_ = lean_usize_land(v_x_1794_, v___x_1799_);
v_j_1801_ = lean_usize_to_nat(v___x_1800_);
v___x_1802_ = lean_array_get_size(v_es_1798_);
v___x_1803_ = lean_nat_dec_lt(v_j_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec(v_j_1801_);
lean_dec(v_x_1797_);
lean_dec(v_x_1796_);
return v_x_1793_;
}
else
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1842_; 
lean_inc_ref(v_es_1798_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_x_1793_, 0);
lean_dec(v_unused_1843_);
v___x_1805_ = v_x_1793_;
v_isShared_1806_ = v_isSharedCheck_1842_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v_x_1793_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1842_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_v_1807_; lean_object* v___x_1808_; lean_object* v_xs_x27_1809_; lean_object* v___y_1811_; 
v_v_1807_ = lean_array_fget(v_es_1798_, v_j_1801_);
v___x_1808_ = lean_box(0);
v_xs_x27_1809_ = lean_array_fset(v_es_1798_, v_j_1801_, v___x_1808_);
switch(lean_obj_tag(v_v_1807_))
{
case 0:
{
lean_object* v_key_1816_; lean_object* v_val_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1827_; 
v_key_1816_ = lean_ctor_get(v_v_1807_, 0);
v_val_1817_ = lean_ctor_get(v_v_1807_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_v_1807_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1819_ = v_v_1807_;
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_val_1817_);
lean_inc(v_key_1816_);
lean_dec(v_v_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Lean_instBEqMVarId_beq(v_x_1796_, v_key_1816_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_del_object(v___x_1819_);
v___x_1822_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1816_, v_val_1817_, v_x_1796_, v_x_1797_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
v___y_1811_ = v___x_1823_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_val_1817_);
lean_dec(v_key_1816_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v_x_1797_);
lean_ctor_set(v___x_1819_, 0, v_x_1796_);
v___x_1825_ = v___x_1819_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_x_1796_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_x_1797_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1811_ = v___x_1825_;
goto v___jp_1810_;
}
}
}
}
case 1:
{
lean_object* v_node_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1840_; 
v_node_1828_ = lean_ctor_get(v_v_1807_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_v_1807_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1830_ = v_v_1807_;
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_node_1828_);
lean_dec(v_v_1807_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
size_t v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1832_ = ((size_t)5ULL);
v___x_1833_ = lean_usize_shift_right(v_x_1794_, v___x_1832_);
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_x_1795_, v___x_1834_);
v___x_1836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1828_, v___x_1833_, v___x_1835_, v_x_1796_, v_x_1797_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1836_);
v___x_1838_ = v___x_1830_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
v___y_1811_ = v___x_1838_;
goto v___jp_1810_;
}
}
}
default: 
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_x_1796_);
lean_ctor_set(v___x_1841_, 1, v_x_1797_);
v___y_1811_ = v___x_1841_;
goto v___jp_1810_;
}
}
v___jp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_array_fset(v_xs_x27_1809_, v_j_1801_, v___y_1811_);
lean_dec(v_j_1801_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1812_);
v___x_1814_ = v___x_1805_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_object* v_ks_1844_; lean_object* v_vs_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1863_; 
v_ks_1844_ = lean_ctor_get(v_x_1793_, 0);
v_vs_1845_ = lean_ctor_get(v_x_1793_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1847_ = v_x_1793_;
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_vs_1845_);
lean_inc(v_ks_1844_);
lean_dec(v_x_1793_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1863_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_ks_1844_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_vs_1845_);
v___x_1850_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v_newNode_1851_; size_t v___x_1852_; uint8_t v___x_1853_; 
v_newNode_1851_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1850_, v_x_1796_, v_x_1797_);
v___x_1852_ = ((size_t)7ULL);
v___x_1853_ = lean_usize_dec_le(v___x_1852_, v_x_1795_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1851_);
v___x_1855_ = lean_unsigned_to_nat(4u);
v___x_1856_ = lean_nat_dec_lt(v___x_1854_, v___x_1855_);
lean_dec(v___x_1854_);
if (v___x_1856_ == 0)
{
lean_object* v_ks_1857_; lean_object* v_vs_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_ks_1857_ = lean_ctor_get(v_newNode_1851_, 0);
lean_inc_ref(v_ks_1857_);
v_vs_1858_ = lean_ctor_get(v_newNode_1851_, 1);
lean_inc_ref(v_vs_1858_);
lean_dec_ref(v_newNode_1851_);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1795_, v_ks_1857_, v_vs_1858_, v___x_1859_, v___x_1860_);
lean_dec_ref(v_vs_1858_);
lean_dec_ref(v_ks_1857_);
return v___x_1861_;
}
else
{
return v_newNode_1851_;
}
}
else
{
return v_newNode_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1864_, lean_object* v_keys_1865_, lean_object* v_vals_1866_, lean_object* v_i_1867_, lean_object* v_entries_1868_){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_array_get_size(v_keys_1865_);
v___x_1870_ = lean_nat_dec_lt(v_i_1867_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec(v_i_1867_);
return v_entries_1868_;
}
else
{
lean_object* v_k_1871_; lean_object* v_v_1872_; uint64_t v___x_1873_; size_t v_h_1874_; size_t v___x_1875_; lean_object* v___x_1876_; size_t v___x_1877_; size_t v___x_1878_; size_t v___x_1879_; size_t v_h_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_k_1871_ = lean_array_fget_borrowed(v_keys_1865_, v_i_1867_);
v_v_1872_ = lean_array_fget_borrowed(v_vals_1866_, v_i_1867_);
v___x_1873_ = l_Lean_instHashableMVarId_hash(v_k_1871_);
v_h_1874_ = lean_uint64_to_usize(v___x_1873_);
v___x_1875_ = ((size_t)5ULL);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_sub(v_depth_1864_, v___x_1877_);
v___x_1879_ = lean_usize_mul(v___x_1875_, v___x_1878_);
v_h_1880_ = lean_usize_shift_right(v_h_1874_, v___x_1879_);
v___x_1881_ = lean_nat_add(v_i_1867_, v___x_1876_);
lean_dec(v_i_1867_);
lean_inc(v_v_1872_);
lean_inc(v_k_1871_);
v___x_1882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1868_, v_h_1880_, v_depth_1864_, v_k_1871_, v_v_1872_);
v_i_1867_ = v___x_1881_;
v_entries_1868_ = v___x_1882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1884_, lean_object* v_keys_1885_, lean_object* v_vals_1886_, lean_object* v_i_1887_, lean_object* v_entries_1888_){
_start:
{
size_t v_depth_boxed_1889_; lean_object* v_res_1890_; 
v_depth_boxed_1889_ = lean_unbox_usize(v_depth_1884_);
lean_dec(v_depth_1884_);
v_res_1890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1889_, v_keys_1885_, v_vals_1886_, v_i_1887_, v_entries_1888_);
lean_dec_ref(v_vals_1886_);
lean_dec_ref(v_keys_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
size_t v_x_1147__boxed_1896_; size_t v_x_1148__boxed_1897_; lean_object* v_res_1898_; 
v_x_1147__boxed_1896_ = lean_unbox_usize(v_x_1892_);
lean_dec(v_x_1892_);
v_x_1148__boxed_1897_ = lean_unbox_usize(v_x_1893_);
lean_dec(v_x_1893_);
v_res_1898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1891_, v_x_1147__boxed_1896_, v_x_1148__boxed_1897_, v_x_1894_, v_x_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
uint64_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = l_Lean_instHashableMVarId_hash(v_x_1900_);
v___x_1903_ = lean_uint64_to_usize(v___x_1902_);
v___x_1904_ = ((size_t)1ULL);
v___x_1905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1899_, v___x_1903_, v___x_1904_, v_x_1900_, v_x_1901_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1906_, lean_object* v_val_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v_mctx_1911_; lean_object* v_cache_1912_; lean_object* v_zetaDeltaFVarIds_1913_; lean_object* v_postponed_1914_; lean_object* v_diag_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1943_; 
v___x_1910_ = lean_st_ref_take(v___y_1908_);
v_mctx_1911_ = lean_ctor_get(v___x_1910_, 0);
v_cache_1912_ = lean_ctor_get(v___x_1910_, 1);
v_zetaDeltaFVarIds_1913_ = lean_ctor_get(v___x_1910_, 2);
v_postponed_1914_ = lean_ctor_get(v___x_1910_, 3);
v_diag_1915_ = lean_ctor_get(v___x_1910_, 4);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1917_ = v___x_1910_;
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_diag_1915_);
lean_inc(v_postponed_1914_);
lean_inc(v_zetaDeltaFVarIds_1913_);
lean_inc(v_cache_1912_);
lean_inc(v_mctx_1911_);
lean_dec(v___x_1910_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_depth_1919_; lean_object* v_levelAssignDepth_1920_; lean_object* v_lmvarCounter_1921_; lean_object* v_mvarCounter_1922_; lean_object* v_lDecls_1923_; lean_object* v_decls_1924_; lean_object* v_userNames_1925_; lean_object* v_lAssignment_1926_; lean_object* v_eAssignment_1927_; lean_object* v_dAssignment_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1942_; 
v_depth_1919_ = lean_ctor_get(v_mctx_1911_, 0);
v_levelAssignDepth_1920_ = lean_ctor_get(v_mctx_1911_, 1);
v_lmvarCounter_1921_ = lean_ctor_get(v_mctx_1911_, 2);
v_mvarCounter_1922_ = lean_ctor_get(v_mctx_1911_, 3);
v_lDecls_1923_ = lean_ctor_get(v_mctx_1911_, 4);
v_decls_1924_ = lean_ctor_get(v_mctx_1911_, 5);
v_userNames_1925_ = lean_ctor_get(v_mctx_1911_, 6);
v_lAssignment_1926_ = lean_ctor_get(v_mctx_1911_, 7);
v_eAssignment_1927_ = lean_ctor_get(v_mctx_1911_, 8);
v_dAssignment_1928_ = lean_ctor_get(v_mctx_1911_, 9);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_mctx_1911_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1930_ = v_mctx_1911_;
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_dAssignment_1928_);
lean_inc(v_eAssignment_1927_);
lean_inc(v_lAssignment_1926_);
lean_inc(v_userNames_1925_);
lean_inc(v_decls_1924_);
lean_inc(v_lDecls_1923_);
lean_inc(v_mvarCounter_1922_);
lean_inc(v_lmvarCounter_1921_);
lean_inc(v_levelAssignDepth_1920_);
lean_inc(v_depth_1919_);
lean_dec(v_mctx_1911_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1942_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1927_, v_mvarId_1906_, v_val_1907_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 8, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_depth_1919_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_levelAssignDepth_1920_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_lmvarCounter_1921_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_mvarCounter_1922_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_lDecls_1923_);
lean_ctor_set(v_reuseFailAlloc_1941_, 5, v_decls_1924_);
lean_ctor_set(v_reuseFailAlloc_1941_, 6, v_userNames_1925_);
lean_ctor_set(v_reuseFailAlloc_1941_, 7, v_lAssignment_1926_);
lean_ctor_set(v_reuseFailAlloc_1941_, 8, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1941_, 9, v_dAssignment_1928_);
v___x_1935_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1935_);
v___x_1937_ = v___x_1917_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_cache_1912_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_zetaDeltaFVarIds_1913_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_postponed_1914_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_diag_1915_);
v___x_1937_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_st_ref_put(v___y_1908_, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1932_);
return v___x_1939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1944_, lean_object* v_val_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1944_, v_val_1945_, v___y_1946_);
lean_dec(v___y_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; 
lean_inc(v_a_1953_);
lean_inc_ref(v_a_1952_);
lean_inc(v_a_1951_);
lean_inc_ref(v_a_1950_);
lean_inc_ref(v_type_1949_);
v___x_1955_ = lean_infer_type(v_type_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Meta_whnfD(v_a_1956_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1992_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1992_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1992_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
switch(lean_obj_tag(v_a_1958_))
{
case 3:
{
lean_object* v_u_1962_; lean_object* v___x_1964_; 
lean_dec_ref(v_type_1949_);
v_u_1962_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_u_1962_);
lean_dec_ref_known(v_a_1958_, 1);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_u_1962_);
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_u_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
case 2:
{
lean_object* v_mvarId_1966_; lean_object* v___x_1967_; 
lean_del_object(v___x_1960_);
v_mvarId_1966_ = lean_ctor_get(v_a_1958_, 0);
lean_inc_n(v_mvarId_1966_, 2);
lean_dec_ref_known(v_a_1958_, 1);
v___x_1967_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1966_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; uint8_t v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref(v_type_1949_);
v___x_1970_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc_n(v_a_1971_, 2);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l_Lean_mkSort(v_a_1971_);
v___x_1973_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1966_, v___x_1972_, v_a_1951_);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v___x_1973_, 0);
lean_dec(v_unused_1981_);
v___x_1975_ = v___x_1973_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_dec(v___x_1973_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v_a_1971_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1971_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_dec(v_mvarId_1966_);
return v___x_1970_;
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_mvarId_1966_);
v___x_1982_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1982_;
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_mvarId_1966_);
lean_dec_ref(v_type_1949_);
v_a_1983_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1967_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1967_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
default: 
{
lean_object* v___x_1991_; 
lean_del_object(v___x_1960_);
lean_dec(v_a_1958_);
v___x_1991_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_type_1949_);
v_a_1993_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1957_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1957_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_type_1949_);
v_a_2001_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1955_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1955_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_getLevel(v_type_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2016_, lean_object* v_val_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2016_, v_val_2017_, v___y_2019_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2024_, lean_object* v_val_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2024_, v_val_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2033_, v_x_2034_, v_x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, size_t v_x_2039_, size_t v_x_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2038_, v_x_2039_, v_x_2040_, v_x_2041_, v_x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
size_t v_x_1496__boxed_2050_; size_t v_x_1497__boxed_2051_; lean_object* v_res_2052_; 
v_x_1496__boxed_2050_ = lean_unbox_usize(v_x_2046_);
lean_dec(v_x_2046_);
v_x_1497__boxed_2051_ = lean_unbox_usize(v_x_2047_);
lean_dec(v_x_2047_);
v_res_2052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2044_, v_x_2045_, v_x_1496__boxed_2050_, v_x_1497__boxed_2051_, v_x_2048_, v_x_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2053_, lean_object* v_n_2054_, lean_object* v_k_2055_, lean_object* v_v_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2054_, v_k_2055_, v_v_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2058_, size_t v_depth_2059_, lean_object* v_keys_2060_, lean_object* v_vals_2061_, lean_object* v_heq_2062_, lean_object* v_i_2063_, lean_object* v_entries_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2059_, v_keys_2060_, v_vals_2061_, v_i_2063_, v_entries_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2066_, lean_object* v_depth_2067_, lean_object* v_keys_2068_, lean_object* v_vals_2069_, lean_object* v_heq_2070_, lean_object* v_i_2071_, lean_object* v_entries_2072_){
_start:
{
size_t v_depth_boxed_2073_; lean_object* v_res_2074_; 
v_depth_boxed_2073_ = lean_unbox_usize(v_depth_2067_);
lean_dec(v_depth_2067_);
v_res_2074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2066_, v_depth_boxed_2073_, v_keys_2068_, v_vals_2069_, v_heq_2070_, v_i_2071_, v_entries_2072_);
lean_dec_ref(v_vals_2069_);
lean_dec_ref(v_keys_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2076_, v_x_2077_, v_x_2078_, v_x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2081_, lean_object* v_b_2082_, lean_object* v_c_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
v___x_2089_ = lean_apply_7(v_k_2081_, v_b_2082_, v_c_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, lean_box(0));
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2090_, lean_object* v_b_2091_, lean_object* v_c_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2090_, v_b_2091_, v_c_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2099_, lean_object* v_k_2100_, uint8_t v_cleanupAnnotations_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___f_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___f_2107_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2107_, 0, v_k_2100_);
v___x_2108_ = 0;
v___x_2109_ = lean_box(0);
v___x_2110_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2108_, v___x_2109_, v_type_2099_, v___f_2107_, v_cleanupAnnotations_2101_, v___x_2108_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
v_a_2119_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2110_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2110_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2127_, lean_object* v_k_2128_, lean_object* v_cleanupAnnotations_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2135_; lean_object* v_res_2136_; 
v_cleanupAnnotations_boxed_2135_ = lean_unbox(v_cleanupAnnotations_2129_);
v_res_2136_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2127_, v_k_2128_, v_cleanupAnnotations_boxed_2135_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2137_, lean_object* v_type_2138_, lean_object* v_k_2139_, uint8_t v_cleanupAnnotations_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2138_, v_k_2139_, v_cleanupAnnotations_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_type_2148_, lean_object* v_k_2149_, lean_object* v_cleanupAnnotations_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2156_; lean_object* v_res_2157_; 
v_cleanupAnnotations_boxed_2156_ = lean_unbox(v_cleanupAnnotations_2150_);
v_res_2157_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2147_, v_type_2148_, v_k_2149_, v_cleanupAnnotations_boxed_2156_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2158_, size_t v_i_2159_, size_t v_stop_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_eq(v_i_2159_, v_stop_2160_);
if (v___x_2167_ == 0)
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_sub(v_i_2159_, v___x_2168_);
v___x_2170_ = lean_array_uget_borrowed(v_as_2158_, v___x_2169_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
lean_inc(v___y_2163_);
lean_inc_ref(v___y_2162_);
lean_inc(v___x_2170_);
v___x_2171_ = lean_infer_type(v___x_2170_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l_Lean_Meta_getLevel(v_a_2172_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = l_Lean_mkLevelIMax_x27(v_a_2174_, v_b_2161_);
v_i_2159_ = v___x_2169_;
v_b_2161_ = v___x_2175_;
goto _start;
}
else
{
lean_dec(v_b_2161_);
return v___x_2173_;
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_b_2161_);
v_a_2177_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2171_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2171_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_b_2161_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2186_, lean_object* v_i_2187_, lean_object* v_stop_2188_, lean_object* v_b_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
size_t v_i_boxed_2195_; size_t v_stop_boxed_2196_; lean_object* v_res_2197_; 
v_i_boxed_2195_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_stop_boxed_2196_ = lean_unbox_usize(v_stop_2188_);
lean_dec(v_stop_2188_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2186_, v_i_boxed_2195_, v_stop_boxed_2196_, v_b_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec_ref(v_as_2186_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2198_, lean_object* v_e_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_a_2206_; lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Meta_getLevel(v_e_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2212_ = lean_array_get_size(v_xs_2198_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_dec_lt(v___x_2213_, v___x_2212_);
if (v___x_2214_ == 0)
{
v_a_2206_ = v_a_2211_;
goto v___jp_2205_;
}
else
{
size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_usize_of_nat(v___x_2212_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2198_, v___x_2215_, v___x_2216_, v_a_2211_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v_a_2206_ = v_a_2218_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2217_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2217_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_a_2227_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2210_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2210_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
v___jp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_Level_normalize(v_a_2206_);
lean_dec(v_a_2206_);
v___x_2208_ = l_Lean_mkSort(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2235_, lean_object* v_e_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2235_, v_e_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_xs_2235_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___f_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v___f_2250_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2251_ = 0;
v___x_2252_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2244_, v___f_2250_, v___x_2251_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2260_, lean_object* v_k_2261_, uint8_t v_cleanupAnnotations_2262_, uint8_t v_preserveNondepLet_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___f_2269_; uint8_t v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2269_, 0, v_k_2261_);
v___x_2270_ = 1;
v___x_2271_ = 0;
v___x_2272_ = lean_box(0);
v___x_2273_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2260_, v___x_2270_, v___x_2270_, v_preserveNondepLet_2263_, v___x_2271_, v___x_2272_, v___f_2269_, v_cleanupAnnotations_2262_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_a_2282_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2273_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2273_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2290_, lean_object* v_k_2291_, lean_object* v_cleanupAnnotations_2292_, lean_object* v_preserveNondepLet_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2299_; uint8_t v_preserveNondepLet_boxed_2300_; lean_object* v_res_2301_; 
v_cleanupAnnotations_boxed_2299_ = lean_unbox(v_cleanupAnnotations_2292_);
v_preserveNondepLet_boxed_2300_ = lean_unbox(v_preserveNondepLet_2293_);
v_res_2301_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2290_, v_k_2291_, v_cleanupAnnotations_boxed_2299_, v_preserveNondepLet_boxed_2300_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2302_, lean_object* v_e_2303_, lean_object* v_k_2304_, uint8_t v_cleanupAnnotations_2305_, uint8_t v_preserveNondepLet_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2303_, v_k_2304_, v_cleanupAnnotations_2305_, v_preserveNondepLet_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_e_2314_, lean_object* v_k_2315_, lean_object* v_cleanupAnnotations_2316_, lean_object* v_preserveNondepLet_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2323_; uint8_t v_preserveNondepLet_boxed_2324_; lean_object* v_res_2325_; 
v_cleanupAnnotations_boxed_2323_ = lean_unbox(v_cleanupAnnotations_2316_);
v_preserveNondepLet_boxed_2324_ = lean_unbox(v_preserveNondepLet_2317_);
v_res_2325_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2313_, v_e_2314_, v_k_2315_, v_cleanupAnnotations_boxed_2323_, v_preserveNondepLet_boxed_2324_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2326_, lean_object* v_e_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
v___x_2333_ = lean_infer_type(v_e_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = 0;
v___x_2336_ = 1;
v___x_2337_ = 1;
v___x_2338_ = l_Lean_Meta_mkForallFVars(v_xs_2326_, v_a_2334_, v___x_2335_, v___x_2336_, v___x_2335_, v___x_2337_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2338_;
}
else
{
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2339_, lean_object* v_e_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2339_, v_e_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_xs_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___f_2354_; uint8_t v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; 
v___f_2354_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2355_ = 0;
v___x_2356_ = 1;
v___x_2357_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2348_, v___f_2354_, v___x_2355_, v___x_2356_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2364_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2367_ = l_Lean_stringToMessageData(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2377_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2378_ = l_Lean_MessageData_ofName(v_mvarId_2371_);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2381_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2390_, lean_object* v_mvarId_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2398_, lean_object* v_mvarId_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2398_, v_mvarId_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_mctx_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_st_ref_get(v_a_2408_);
v_mctx_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_mctx_2413_);
lean_dec(v___x_2412_);
v___x_2414_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2413_, v_mvarId_2406_);
lean_dec_ref(v_mctx_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
return v___x_2415_;
}
else
{
lean_object* v_val_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_mvarId_2406_);
v_val_2416_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2414_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_val_2416_);
lean_dec(v___x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_type_2420_; lean_object* v___x_2422_; 
v_type_2420_ = lean_ctor_get(v_val_2416_, 2);
lean_inc_ref(v_type_2420_);
lean_dec(v_val_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 0);
lean_ctor_set(v___x_2418_, 0, v_type_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_type_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_lctx_2437_; lean_object* v___x_2438_; 
v_lctx_2437_ = lean_ctor_get(v_a_2433_, 2);
lean_inc(v_fvarId_2432_);
lean_inc_ref(v_lctx_2437_);
v___x_2438_ = lean_local_ctx_find(v_lctx_2437_, v_fvarId_2432_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2432_, v_a_2434_, v_a_2435_);
return v___x_2439_;
}
else
{
lean_object* v_val_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_fvarId_2432_);
v_val_2440_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2442_ = v___x_2438_;
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_val_2440_);
lean_dec(v___x_2438_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = l_Lean_LocalDecl_type(v_val_2440_);
lean_dec(v_val_2440_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2455_, v_a_2456_, v_a_2458_, v_a_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(lean_object* v_a_2469_, lean_object* v_b_2470_){
_start:
{
lean_object* v_expr_2471_; uint64_t v_configKey_2472_; lean_object* v_expr_2473_; uint64_t v_configKey_2474_; uint64_t v___x_2475_; uint64_t v___x_2476_; uint64_t v___x_2477_; uint64_t v___x_2478_; uint8_t v___x_2479_; 
v_expr_2471_ = lean_ctor_get(v_a_2469_, 0);
v_configKey_2472_ = lean_ctor_get_uint64(v_a_2469_, sizeof(void*)*1);
v_expr_2473_ = lean_ctor_get(v_b_2470_, 0);
v_configKey_2474_ = lean_ctor_get_uint64(v_b_2470_, sizeof(void*)*1);
v___x_2475_ = l_Lean_Expr_hash(v_expr_2471_);
v___x_2476_ = lean_uint64_mix_hash(v___x_2475_, v_configKey_2472_);
v___x_2477_ = l_Lean_Expr_hash(v_expr_2473_);
v___x_2478_ = lean_uint64_mix_hash(v___x_2477_, v_configKey_2474_);
v___x_2479_ = lean_uint64_dec_eq(v___x_2476_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0___boxed(lean_object* v_a_2480_, lean_object* v_b_2481_){
_start:
{
uint8_t v_res_2482_; lean_object* v_r_2483_; 
v_res_2482_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(v_a_2480_, v_b_2481_);
lean_dec_ref(v_b_2481_);
lean_dec_ref(v_a_2480_);
v_r_2483_ = lean_box(v_res_2482_);
return v_r_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_instMonadEIO___redArg();
return v___x_2484_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2486_ = l_StateRefT_x27_instMonad___redArg(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_instMonadExceptOfEIO___redArg();
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___f_2491_; 
v___x_2490_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2491_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2491_, 0, v___x_2490_);
return v___f_2491_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___f_2493_; 
v___x_2492_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2493_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2493_, 0, v___x_2492_);
return v___f_2493_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; 
v___f_2494_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2495_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___f_2495_);
lean_ctor_set(v___x_2496_, 1, v___f_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___f_2498_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2498_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2498_, 0, v___x_2497_);
return v___f_2498_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___f_2500_; 
v___x_2499_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2500_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2500_, 0, v___x_2499_);
return v___f_2500_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; 
v___f_2501_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2502_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___f_2502_);
lean_ctor_set(v___x_2503_, 1, v___f_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2506_, lean_object* v_inferType_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
uint8_t v_cacheInferType_2552_; 
v_cacheInferType_2552_ = lean_ctor_get_uint8(v_a_2508_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2552_ == 0)
{
lean_dec_ref(v_e_2506_);
goto v___jp_2513_;
}
else
{
uint8_t v___x_2553_; 
v___x_2553_ = l_Lean_Expr_hasMVar(v_e_2506_);
if (v___x_2553_ == 0)
{
lean_object* v___f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___f_2554_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2556_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2506_, v_a_2508_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2684_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2684_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2684_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2638_; lean_object* v_cache_2639_; lean_object* v_inferType_2640_; lean_object* v___x_2641_; 
v___x_2638_ = lean_st_ref_get(v_a_2509_);
v_cache_2639_ = lean_ctor_get(v___x_2638_, 1);
lean_inc_ref(v_cache_2639_);
lean_dec(v___x_2638_);
v_inferType_2640_ = lean_ctor_get(v_cache_2639_, 0);
lean_inc_ref(v_inferType_2640_);
lean_dec_ref(v_cache_2639_);
lean_inc(v_a_2557_);
v___x_2641_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_2554_, v___x_2555_, v_inferType_2640_, v_a_2557_);
if (lean_obj_tag(v___x_2641_) == 1)
{
lean_object* v_val_2642_; lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v_expr_2645_; uint64_t v_configKey_2646_; lean_object* v_expr_2647_; uint64_t v_configKey_2648_; uint8_t v___x_2649_; 
v_val_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_val_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v_fst_2643_ = lean_ctor_get(v_val_2642_, 0);
lean_inc(v_fst_2643_);
v_snd_2644_ = lean_ctor_get(v_val_2642_, 1);
lean_inc(v_snd_2644_);
lean_dec(v_val_2642_);
v_expr_2645_ = lean_ctor_get(v_a_2557_, 0);
v_configKey_2646_ = lean_ctor_get_uint64(v_a_2557_, sizeof(void*)*1);
v_expr_2647_ = lean_ctor_get(v_fst_2643_, 0);
lean_inc_ref(v_expr_2647_);
v_configKey_2648_ = lean_ctor_get_uint64(v_fst_2643_, sizeof(void*)*1);
lean_dec(v_fst_2643_);
v___x_2649_ = lean_uint64_dec_eq(v_configKey_2646_, v_configKey_2648_);
if (v___x_2649_ == 0)
{
lean_dec_ref(v_expr_2647_);
lean_dec(v_snd_2644_);
lean_dec_ref(v_inferType_2640_);
lean_del_object(v___x_2559_);
goto v___jp_2602_;
}
else
{
size_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = ((size_t)64ULL);
v___x_2651_ = lean_expr_equal_budgeted(v_expr_2645_, v_expr_2647_, v___x_2650_);
lean_dec_ref(v_expr_2647_);
switch(v___x_2651_)
{
case 0:
{
lean_dec(v_snd_2644_);
lean_dec_ref(v_inferType_2640_);
lean_del_object(v___x_2559_);
goto v___jp_2602_;
}
case 1:
{
lean_object* v___x_2653_; 
lean_dec_ref(v_inferType_2640_);
lean_dec(v_a_2557_);
lean_dec_ref(v_inferType_2507_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_snd_2644_);
v___x_2653_ = v___x_2559_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_snd_2644_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
default: 
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v_cache_2657_; lean_object* v_mctx_2658_; lean_object* v_zetaDeltaFVarIds_2659_; lean_object* v_postponed_2660_; lean_object* v_diag_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_snd_2644_);
lean_del_object(v___x_2559_);
lean_inc(v_a_2557_);
v___x_2655_ = l_Lean_PersistentHashMap_erase___redArg(v___f_2554_, v___x_2555_, v_inferType_2640_, v_a_2557_);
v___x_2656_ = lean_st_ref_take(v_a_2509_);
v_cache_2657_ = lean_ctor_get(v___x_2656_, 1);
v_mctx_2658_ = lean_ctor_get(v___x_2656_, 0);
v_zetaDeltaFVarIds_2659_ = lean_ctor_get(v___x_2656_, 2);
v_postponed_2660_ = lean_ctor_get(v___x_2656_, 3);
v_diag_2661_ = lean_ctor_get(v___x_2656_, 4);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2663_ = v___x_2656_;
v_isShared_2664_ = v_isSharedCheck_2683_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_diag_2661_);
lean_inc(v_postponed_2660_);
lean_inc(v_zetaDeltaFVarIds_2659_);
lean_inc(v_cache_2657_);
lean_inc(v_mctx_2658_);
lean_dec(v___x_2656_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2683_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_funInfo_2665_; lean_object* v_synthInstance_2666_; lean_object* v_whnf_2667_; lean_object* v_defEqTrans_2668_; lean_object* v_defEqPerm_2669_; lean_object* v_unfold_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2681_; 
v_funInfo_2665_ = lean_ctor_get(v_cache_2657_, 1);
v_synthInstance_2666_ = lean_ctor_get(v_cache_2657_, 2);
v_whnf_2667_ = lean_ctor_get(v_cache_2657_, 3);
v_defEqTrans_2668_ = lean_ctor_get(v_cache_2657_, 4);
v_defEqPerm_2669_ = lean_ctor_get(v_cache_2657_, 5);
v_unfold_2670_ = lean_ctor_get(v_cache_2657_, 6);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_cache_2657_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v_cache_2657_, 0);
lean_dec(v_unused_2682_);
v___x_2672_ = v_cache_2657_;
v_isShared_2673_ = v_isSharedCheck_2681_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_unfold_2670_);
lean_inc(v_defEqPerm_2669_);
lean_inc(v_defEqTrans_2668_);
lean_inc(v_whnf_2667_);
lean_inc(v_synthInstance_2666_);
lean_inc(v_funInfo_2665_);
lean_dec(v_cache_2657_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2681_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2655_);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_funInfo_2665_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_synthInstance_2666_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_whnf_2667_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_defEqTrans_2668_);
lean_ctor_set(v_reuseFailAlloc_2680_, 5, v_defEqPerm_2669_);
lean_ctor_set(v_reuseFailAlloc_2680_, 6, v_unfold_2670_);
v___x_2675_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2675_);
v___x_2677_ = v___x_2663_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_mctx_2658_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_zetaDeltaFVarIds_2659_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_postponed_2660_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_diag_2661_);
v___x_2677_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_st_ref_put(v_a_2509_, v___x_2677_);
goto v___jp_2602_;
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
lean_dec(v___x_2641_);
lean_dec_ref(v_inferType_2640_);
lean_del_object(v___x_2559_);
goto v___jp_2602_;
}
v___jp_2561_:
{
lean_object* v___x_2562_; 
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
lean_inc(v_a_2509_);
lean_inc_ref(v_a_2508_);
v___x_2562_ = lean_apply_5(v_inferType_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, lean_box(0));
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; uint8_t v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
v___x_2564_ = l_Lean_Expr_hasMVar(v_a_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2600_; 
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v___x_2562_, 0);
lean_dec(v_unused_2601_);
v___x_2566_ = v___x_2562_;
v_isShared_2567_ = v_isSharedCheck_2600_;
goto v_resetjp_2565_;
}
else
{
lean_dec(v___x_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2600_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v_cache_2569_; lean_object* v_mctx_2570_; lean_object* v_zetaDeltaFVarIds_2571_; lean_object* v_postponed_2572_; lean_object* v_diag_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2599_; 
v___x_2568_ = lean_st_ref_take(v_a_2509_);
v_cache_2569_ = lean_ctor_get(v___x_2568_, 1);
v_mctx_2570_ = lean_ctor_get(v___x_2568_, 0);
v_zetaDeltaFVarIds_2571_ = lean_ctor_get(v___x_2568_, 2);
v_postponed_2572_ = lean_ctor_get(v___x_2568_, 3);
v_diag_2573_ = lean_ctor_get(v___x_2568_, 4);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2575_ = v___x_2568_;
v_isShared_2576_ = v_isSharedCheck_2599_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_diag_2573_);
lean_inc(v_postponed_2572_);
lean_inc(v_zetaDeltaFVarIds_2571_);
lean_inc(v_cache_2569_);
lean_inc(v_mctx_2570_);
lean_dec(v___x_2568_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2599_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_inferType_2577_; lean_object* v_funInfo_2578_; lean_object* v_synthInstance_2579_; lean_object* v_whnf_2580_; lean_object* v_defEqTrans_2581_; lean_object* v_defEqPerm_2582_; lean_object* v_unfold_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2598_; 
v_inferType_2577_ = lean_ctor_get(v_cache_2569_, 0);
v_funInfo_2578_ = lean_ctor_get(v_cache_2569_, 1);
v_synthInstance_2579_ = lean_ctor_get(v_cache_2569_, 2);
v_whnf_2580_ = lean_ctor_get(v_cache_2569_, 3);
v_defEqTrans_2581_ = lean_ctor_get(v_cache_2569_, 4);
v_defEqPerm_2582_ = lean_ctor_get(v_cache_2569_, 5);
v_unfold_2583_ = lean_ctor_get(v_cache_2569_, 6);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_cache_2569_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2585_ = v_cache_2569_;
v_isShared_2586_ = v_isSharedCheck_2598_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_unfold_2583_);
lean_inc(v_defEqPerm_2582_);
lean_inc(v_defEqTrans_2581_);
lean_inc(v_whnf_2580_);
lean_inc(v_synthInstance_2579_);
lean_inc(v_funInfo_2578_);
lean_inc(v_inferType_2577_);
lean_dec(v_cache_2569_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2598_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_inc(v_a_2563_);
v___x_2587_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2554_, v___x_2555_, v_inferType_2577_, v_a_2557_, v_a_2563_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_funInfo_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_synthInstance_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_whnf_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_defEqTrans_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_defEqPerm_2582_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_unfold_2583_);
v___x_2589_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2589_);
v___x_2591_ = v___x_2575_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_mctx_2570_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_zetaDeltaFVarIds_2571_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_postponed_2572_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_diag_2573_);
v___x_2591_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_st_ref_put(v_a_2509_, v___x_2591_);
if (v_isShared_2567_ == 0)
{
v___x_2594_ = v___x_2566_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2563_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2563_);
lean_dec(v_a_2557_);
return v___x_2562_;
}
}
else
{
lean_dec(v_a_2557_);
return v___x_2562_;
}
}
v___jp_2602_:
{
lean_object* v___x_2603_; lean_object* v_toApplicative_2604_; lean_object* v_toFunctor_2605_; lean_object* v_toSeq_2606_; lean_object* v_toSeqLeft_2607_; lean_object* v_toSeqRight_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_toCold_2624_; lean_object* v_cancelTk_x3f_2625_; 
v___x_2603_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2604_ = lean_ctor_get(v___x_2603_, 0);
v_toFunctor_2605_ = lean_ctor_get(v_toApplicative_2604_, 0);
v_toSeq_2606_ = lean_ctor_get(v_toApplicative_2604_, 2);
v_toSeqLeft_2607_ = lean_ctor_get(v_toApplicative_2604_, 3);
v_toSeqRight_2608_ = lean_ctor_get(v_toApplicative_2604_, 4);
v___f_2609_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2610_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2605_, 2);
v___f_2611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2611_, 0, v_toFunctor_2605_);
v___f_2612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2612_, 0, v_toFunctor_2605_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___f_2611_);
lean_ctor_set(v___x_2613_, 1, v___f_2612_);
lean_inc(v_toSeqRight_2608_);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toSeqRight_2608_);
lean_inc(v_toSeqLeft_2607_);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toSeqLeft_2607_);
lean_inc(v_toSeq_2606_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toSeq_2606_);
v___x_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2613_);
lean_ctor_set(v___x_2617_, 1, v___f_2609_);
lean_ctor_set(v___x_2617_, 2, v___f_2616_);
lean_ctor_set(v___x_2617_, 3, v___f_2615_);
lean_ctor_set(v___x_2617_, 4, v___f_2614_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___f_2610_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2620_ = l_Lean_Core_instMonadRefCoreM;
v___x_2621_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2622_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2621_, v___x_2618_);
v___x_2623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2619_);
lean_ctor_set(v___x_2623_, 1, v___x_2620_);
lean_ctor_set(v___x_2623_, 2, v___x_2622_);
v_toCold_2624_ = lean_ctor_get(v_a_2510_, 0);
v_cancelTk_x3f_2625_ = lean_ctor_get(v_toCold_2624_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2625_) == 1)
{
lean_object* v_val_2626_; uint8_t v___x_2627_; 
v_val_2626_ = lean_ctor_get(v_cancelTk_x3f_2625_, 0);
v___x_2627_ = l_IO_CancelToken_isSet(v_val_2626_);
if (v___x_2627_ == 0)
{
lean_dec_ref_known(v___x_2623_, 3);
goto v___jp_2561_;
}
else
{
lean_object* v___x_4224__overap_2628_; lean_object* v___x_2629_; 
v___x_4224__overap_2628_ = l_Lean_throwInterruptException___redArg(v___x_2623_);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
v___x_2629_ = lean_apply_3(v___x_4224__overap_2628_, v_a_2510_, v_a_2511_, lean_box(0));
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_dec_ref_known(v___x_2629_, 1);
goto v___jp_2561_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2557_);
lean_dec_ref(v_inferType_2507_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2623_, 3);
goto v___jp_2561_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v_inferType_2507_);
v_a_2685_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2556_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2556_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_dec_ref(v_e_2506_);
goto v___jp_2513_;
}
}
v___jp_2513_:
{
lean_object* v___x_2514_; lean_object* v_toApplicative_2515_; lean_object* v_toFunctor_2516_; lean_object* v_toSeq_2517_; lean_object* v_toSeqLeft_2518_; lean_object* v_toSeqRight_2519_; lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; lean_object* v___f_2525_; lean_object* v___f_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_toCold_2535_; lean_object* v_cancelTk_x3f_2536_; 
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2515_ = lean_ctor_get(v___x_2514_, 0);
v_toFunctor_2516_ = lean_ctor_get(v_toApplicative_2515_, 0);
v_toSeq_2517_ = lean_ctor_get(v_toApplicative_2515_, 2);
v_toSeqLeft_2518_ = lean_ctor_get(v_toApplicative_2515_, 3);
v_toSeqRight_2519_ = lean_ctor_get(v_toApplicative_2515_, 4);
v___f_2520_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2521_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2516_, 2);
v___f_2522_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2522_, 0, v_toFunctor_2516_);
v___f_2523_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2523_, 0, v_toFunctor_2516_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___f_2522_);
lean_ctor_set(v___x_2524_, 1, v___f_2523_);
lean_inc(v_toSeqRight_2519_);
v___f_2525_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2525_, 0, v_toSeqRight_2519_);
lean_inc(v_toSeqLeft_2518_);
v___f_2526_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2526_, 0, v_toSeqLeft_2518_);
lean_inc(v_toSeq_2517_);
v___f_2527_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2527_, 0, v_toSeq_2517_);
v___x_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2524_);
lean_ctor_set(v___x_2528_, 1, v___f_2520_);
lean_ctor_set(v___x_2528_, 2, v___f_2527_);
lean_ctor_set(v___x_2528_, 3, v___f_2526_);
lean_ctor_set(v___x_2528_, 4, v___f_2525_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___f_2521_);
v___x_2530_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2531_ = l_Lean_Core_instMonadRefCoreM;
v___x_2532_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2533_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2532_, v___x_2529_);
v___x_2534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2530_);
lean_ctor_set(v___x_2534_, 1, v___x_2531_);
lean_ctor_set(v___x_2534_, 2, v___x_2533_);
v_toCold_2535_ = lean_ctor_get(v_a_2510_, 0);
v_cancelTk_x3f_2536_ = lean_ctor_get(v_toCold_2535_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2536_) == 1)
{
lean_object* v_val_2537_; uint8_t v___x_2538_; 
v_val_2537_ = lean_ctor_get(v_cancelTk_x3f_2536_, 0);
v___x_2538_ = l_IO_CancelToken_isSet(v_val_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2534_, 3);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
lean_inc(v_a_2509_);
lean_inc_ref(v_a_2508_);
v___x_2539_ = lean_apply_5(v_inferType_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, lean_box(0));
return v___x_2539_;
}
else
{
lean_object* v___x_4199__overap_2540_; lean_object* v___x_2541_; 
v___x_4199__overap_2540_ = l_Lean_throwInterruptException___redArg(v___x_2534_);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
v___x_2541_ = lean_apply_3(v___x_4199__overap_2540_, v_a_2510_, v_a_2511_, lean_box(0));
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; 
lean_dec_ref_known(v___x_2541_, 1);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
lean_inc(v_a_2509_);
lean_inc_ref(v_a_2508_);
v___x_2542_ = lean_apply_5(v_inferType_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, lean_box(0));
return v___x_2542_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_inferType_2507_);
v_a_2543_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2541_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
else
{
lean_object* v___x_2551_; 
lean_dec_ref_known(v___x_2534_, 3);
lean_inc(v_a_2511_);
lean_inc_ref(v_a_2510_);
lean_inc(v_a_2509_);
lean_inc_ref(v_a_2508_);
v___x_2551_ = lean_apply_5(v_inferType_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, lean_box(0));
return v___x_2551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2693_, lean_object* v_inferType_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2693_, v_inferType_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2754_; uint8_t v_beta_2755_; 
v___x_2754_ = l_Lean_Meta_Context_config(v___y_2702_);
v_beta_2755_ = lean_ctor_get_uint8(v___x_2754_, 13);
if (v_beta_2755_ == 0)
{
lean_dec_ref(v___x_2754_);
goto v___jp_2707_;
}
else
{
uint8_t v_iota_2756_; 
v_iota_2756_ = lean_ctor_get_uint8(v___x_2754_, 12);
if (v_iota_2756_ == 0)
{
lean_dec_ref(v___x_2754_);
goto v___jp_2707_;
}
else
{
uint8_t v_zeta_2757_; 
v_zeta_2757_ = lean_ctor_get_uint8(v___x_2754_, 15);
if (v_zeta_2757_ == 0)
{
lean_dec_ref(v___x_2754_);
goto v___jp_2707_;
}
else
{
uint8_t v_zetaHave_2758_; 
v_zetaHave_2758_ = lean_ctor_get_uint8(v___x_2754_, 18);
if (v_zetaHave_2758_ == 0)
{
lean_dec_ref(v___x_2754_);
goto v___jp_2707_;
}
else
{
uint8_t v_zetaDelta_2759_; 
v_zetaDelta_2759_ = lean_ctor_get_uint8(v___x_2754_, 16);
if (v_zetaDelta_2759_ == 0)
{
lean_dec_ref(v___x_2754_);
goto v___jp_2707_;
}
else
{
uint8_t v_etaStruct_2760_; uint8_t v_proj_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_etaStruct_2760_ = lean_ctor_get_uint8(v___x_2754_, 10);
v_proj_2761_ = lean_ctor_get_uint8(v___x_2754_, 14);
lean_dec_ref(v___x_2754_);
v___x_2762_ = lean_box(v_proj_2761_);
v___x_2763_ = lean_obj_tag_nat(v___x_2762_);
lean_dec(v___x_2762_);
v___x_2764_ = lean_unsigned_to_nat(2u);
v___x_2765_ = lean_nat_dec_eq(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
goto v___jp_2707_;
}
else
{
uint8_t v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = 0;
v___x_2767_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2760_, v___x_2766_);
if (v___x_2767_ == 0)
{
goto v___jp_2707_;
}
else
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_apply_5(v_x_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
return v___x_2768_;
}
}
}
}
}
}
}
v___jp_2707_:
{
lean_object* v___x_2708_; uint8_t v_foApprox_2709_; uint8_t v_ctxApprox_2710_; uint8_t v_quasiPatternApprox_2711_; uint8_t v_constApprox_2712_; uint8_t v_isDefEqStuckEx_2713_; uint8_t v_unificationHints_2714_; uint8_t v_proofIrrelevance_2715_; uint8_t v_assignSyntheticOpaque_2716_; uint8_t v_offsetCnstrs_2717_; uint8_t v_transparency_2718_; uint8_t v_univApprox_2719_; uint8_t v_zetaUnused_2720_; uint8_t v_canUnfoldPredicateConfig_2721_; uint8_t v_stringLitToCtor_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2753_; 
v___x_2708_ = l_Lean_Meta_Context_config(v___y_2702_);
v_foApprox_2709_ = lean_ctor_get_uint8(v___x_2708_, 0);
v_ctxApprox_2710_ = lean_ctor_get_uint8(v___x_2708_, 1);
v_quasiPatternApprox_2711_ = lean_ctor_get_uint8(v___x_2708_, 2);
v_constApprox_2712_ = lean_ctor_get_uint8(v___x_2708_, 3);
v_isDefEqStuckEx_2713_ = lean_ctor_get_uint8(v___x_2708_, 4);
v_unificationHints_2714_ = lean_ctor_get_uint8(v___x_2708_, 5);
v_proofIrrelevance_2715_ = lean_ctor_get_uint8(v___x_2708_, 6);
v_assignSyntheticOpaque_2716_ = lean_ctor_get_uint8(v___x_2708_, 7);
v_offsetCnstrs_2717_ = lean_ctor_get_uint8(v___x_2708_, 8);
v_transparency_2718_ = lean_ctor_get_uint8(v___x_2708_, 9);
v_univApprox_2719_ = lean_ctor_get_uint8(v___x_2708_, 11);
v_zetaUnused_2720_ = lean_ctor_get_uint8(v___x_2708_, 17);
v_canUnfoldPredicateConfig_2721_ = lean_ctor_get_uint8(v___x_2708_, 19);
v_stringLitToCtor_2722_ = lean_ctor_get_uint8(v___x_2708_, 20);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2724_ = v___x_2708_;
v_isShared_2725_ = v_isSharedCheck_2753_;
goto v_resetjp_2723_;
}
else
{
lean_dec(v___x_2708_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2753_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___x_2726_; uint8_t v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2730_; 
v___x_2726_ = 1;
v___x_2727_ = 0;
v___x_2728_ = 2;
if (v_isShared_2725_ == 0)
{
v___x_2730_ = v___x_2724_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 0, v_foApprox_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 1, v_ctxApprox_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 2, v_quasiPatternApprox_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 3, v_constApprox_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 4, v_isDefEqStuckEx_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 5, v_unificationHints_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 6, v_proofIrrelevance_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 7, v_assignSyntheticOpaque_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 8, v_offsetCnstrs_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 9, v_transparency_2718_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 11, v_univApprox_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 17, v_zetaUnused_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 19, v_canUnfoldPredicateConfig_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, 20, v_stringLitToCtor_2722_);
v___x_2730_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
uint8_t v_trackZetaDelta_2731_; lean_object* v_zetaDeltaSet_2732_; lean_object* v_lctx_2733_; lean_object* v_localInstances_2734_; lean_object* v_defEqCtx_x3f_2735_; lean_object* v_synthPendingDepth_2736_; lean_object* v_customCanUnfoldPredicate_x3f_2737_; uint8_t v_univApprox_2738_; uint8_t v_inTypeClassResolution_2739_; uint8_t v_cacheInferType_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2750_; 
lean_ctor_set_uint8(v___x_2730_, 10, v___x_2727_);
lean_ctor_set_uint8(v___x_2730_, 12, v___x_2726_);
lean_ctor_set_uint8(v___x_2730_, 13, v___x_2726_);
lean_ctor_set_uint8(v___x_2730_, 14, v___x_2728_);
lean_ctor_set_uint8(v___x_2730_, 15, v___x_2726_);
lean_ctor_set_uint8(v___x_2730_, 16, v___x_2726_);
lean_ctor_set_uint8(v___x_2730_, 18, v___x_2726_);
v_trackZetaDelta_2731_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*7);
v_zetaDeltaSet_2732_ = lean_ctor_get(v___y_2702_, 1);
v_lctx_2733_ = lean_ctor_get(v___y_2702_, 2);
v_localInstances_2734_ = lean_ctor_get(v___y_2702_, 3);
v_defEqCtx_x3f_2735_ = lean_ctor_get(v___y_2702_, 4);
v_synthPendingDepth_2736_ = lean_ctor_get(v___y_2702_, 5);
v_customCanUnfoldPredicate_x3f_2737_ = lean_ctor_get(v___y_2702_, 6);
v_univApprox_2738_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2739_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*7 + 2);
v_cacheInferType_2740_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*7 + 3);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___y_2702_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___y_2702_, 0);
lean_dec(v_unused_2751_);
v___x_2742_ = v___y_2702_;
v_isShared_2743_ = v_isSharedCheck_2750_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2737_);
lean_inc(v_synthPendingDepth_2736_);
lean_inc(v_defEqCtx_x3f_2735_);
lean_inc(v_localInstances_2734_);
lean_inc(v_lctx_2733_);
lean_inc(v_zetaDeltaSet_2732_);
lean_dec(v___y_2702_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2750_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint64_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2744_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2730_);
v___x_2745_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2745_, 0, v___x_2730_);
lean_ctor_set_uint64(v___x_2745_, sizeof(void*)*1, v___x_2744_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2745_);
v___x_2747_ = v___x_2742_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_zetaDeltaSet_2732_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v_lctx_2733_);
lean_ctor_set(v_reuseFailAlloc_2749_, 3, v_localInstances_2734_);
lean_ctor_set(v_reuseFailAlloc_2749_, 4, v_defEqCtx_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2749_, 5, v_synthPendingDepth_2736_);
lean_ctor_set(v_reuseFailAlloc_2749_, 6, v_customCanUnfoldPredicate_x3f_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*7, v_trackZetaDelta_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*7 + 1, v_univApprox_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*7 + 3, v_cacheInferType_2740_);
v___x_2747_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_apply_5(v_x_2701_, v___x_2747_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
return v___x_2748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___y_2783_; lean_object* v___x_2800_; uint8_t v_transparency_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; 
v___x_2800_ = l_Lean_Meta_Context_config(v_a_2777_);
v_transparency_2801_ = lean_ctor_get_uint8(v___x_2800_, 9);
lean_dec_ref(v___x_2800_);
v___x_2802_ = 1;
v___x_2803_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
lean_inc_ref(v_a_2777_);
v___x_2804_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
v___y_2783_ = v___x_2804_;
goto v___jp_2782_;
}
else
{
lean_object* v_keyedConfig_2805_; uint8_t v_trackZetaDelta_2806_; lean_object* v_zetaDeltaSet_2807_; lean_object* v_lctx_2808_; lean_object* v_localInstances_2809_; lean_object* v_defEqCtx_x3f_2810_; lean_object* v_synthPendingDepth_2811_; lean_object* v_customCanUnfoldPredicate_x3f_2812_; uint8_t v_univApprox_2813_; uint8_t v_inTypeClassResolution_2814_; uint8_t v_cacheInferType_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_keyedConfig_2805_ = lean_ctor_get(v_a_2777_, 0);
v_trackZetaDelta_2806_ = lean_ctor_get_uint8(v_a_2777_, sizeof(void*)*7);
v_zetaDeltaSet_2807_ = lean_ctor_get(v_a_2777_, 1);
v_lctx_2808_ = lean_ctor_get(v_a_2777_, 2);
v_localInstances_2809_ = lean_ctor_get(v_a_2777_, 3);
v_defEqCtx_x3f_2810_ = lean_ctor_get(v_a_2777_, 4);
v_synthPendingDepth_2811_ = lean_ctor_get(v_a_2777_, 5);
v_customCanUnfoldPredicate_x3f_2812_ = lean_ctor_get(v_a_2777_, 6);
v_univApprox_2813_ = lean_ctor_get_uint8(v_a_2777_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2814_ = lean_ctor_get_uint8(v_a_2777_, sizeof(void*)*7 + 2);
v_cacheInferType_2815_ = lean_ctor_get_uint8(v_a_2777_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2805_);
v___x_2816_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2802_, v_keyedConfig_2805_);
lean_inc(v_customCanUnfoldPredicate_x3f_2812_);
lean_inc(v_synthPendingDepth_2811_);
lean_inc(v_defEqCtx_x3f_2810_);
lean_inc_ref(v_localInstances_2809_);
lean_inc_ref(v_lctx_2808_);
lean_inc(v_zetaDeltaSet_2807_);
v___x_2817_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v_zetaDeltaSet_2807_);
lean_ctor_set(v___x_2817_, 2, v_lctx_2808_);
lean_ctor_set(v___x_2817_, 3, v_localInstances_2809_);
lean_ctor_set(v___x_2817_, 4, v_defEqCtx_x3f_2810_);
lean_ctor_set(v___x_2817_, 5, v_synthPendingDepth_2811_);
lean_ctor_set(v___x_2817_, 6, v_customCanUnfoldPredicate_x3f_2812_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*7, v_trackZetaDelta_2806_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*7 + 1, v_univApprox_2813_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2814_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*7 + 3, v_cacheInferType_2815_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
v___x_2818_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2776_, v___x_2817_, v_a_2778_, v_a_2779_, v_a_2780_);
v___y_2783_ = v___x_2818_;
goto v___jp_2782_;
}
v___jp_2782_:
{
if (lean_obj_tag(v___y_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_a_2784_ = lean_ctor_get(v___y_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___y_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___y_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___y_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___y_2783_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___y_2783_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___y_2783_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___y_2783_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2826_, lean_object* v_x_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___y_2834_; lean_object* v___x_2851_; uint8_t v_transparency_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; 
v___x_2851_ = l_Lean_Meta_Context_config(v_a_2828_);
v_transparency_2852_ = lean_ctor_get_uint8(v___x_2851_, 9);
lean_dec_ref(v___x_2851_);
v___x_2853_ = 1;
v___x_2854_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_inc(v_a_2831_);
lean_inc_ref(v_a_2830_);
lean_inc(v_a_2829_);
lean_inc_ref(v_a_2828_);
v___x_2855_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
v___y_2834_ = v___x_2855_;
goto v___jp_2833_;
}
else
{
lean_object* v_keyedConfig_2856_; uint8_t v_trackZetaDelta_2857_; lean_object* v_zetaDeltaSet_2858_; lean_object* v_lctx_2859_; lean_object* v_localInstances_2860_; lean_object* v_defEqCtx_x3f_2861_; lean_object* v_synthPendingDepth_2862_; lean_object* v_customCanUnfoldPredicate_x3f_2863_; uint8_t v_univApprox_2864_; uint8_t v_inTypeClassResolution_2865_; uint8_t v_cacheInferType_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_keyedConfig_2856_ = lean_ctor_get(v_a_2828_, 0);
v_trackZetaDelta_2857_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*7);
v_zetaDeltaSet_2858_ = lean_ctor_get(v_a_2828_, 1);
v_lctx_2859_ = lean_ctor_get(v_a_2828_, 2);
v_localInstances_2860_ = lean_ctor_get(v_a_2828_, 3);
v_defEqCtx_x3f_2861_ = lean_ctor_get(v_a_2828_, 4);
v_synthPendingDepth_2862_ = lean_ctor_get(v_a_2828_, 5);
v_customCanUnfoldPredicate_x3f_2863_ = lean_ctor_get(v_a_2828_, 6);
v_univApprox_2864_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2865_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*7 + 2);
v_cacheInferType_2866_ = lean_ctor_get_uint8(v_a_2828_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2856_);
v___x_2867_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2853_, v_keyedConfig_2856_);
lean_inc(v_customCanUnfoldPredicate_x3f_2863_);
lean_inc(v_synthPendingDepth_2862_);
lean_inc(v_defEqCtx_x3f_2861_);
lean_inc_ref(v_localInstances_2860_);
lean_inc_ref(v_lctx_2859_);
lean_inc(v_zetaDeltaSet_2858_);
v___x_2868_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
lean_ctor_set(v___x_2868_, 1, v_zetaDeltaSet_2858_);
lean_ctor_set(v___x_2868_, 2, v_lctx_2859_);
lean_ctor_set(v___x_2868_, 3, v_localInstances_2860_);
lean_ctor_set(v___x_2868_, 4, v_defEqCtx_x3f_2861_);
lean_ctor_set(v___x_2868_, 5, v_synthPendingDepth_2862_);
lean_ctor_set(v___x_2868_, 6, v_customCanUnfoldPredicate_x3f_2863_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*7, v_trackZetaDelta_2857_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*7 + 1, v_univApprox_2864_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2865_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*7 + 3, v_cacheInferType_2866_);
lean_inc(v_a_2831_);
lean_inc_ref(v_a_2830_);
lean_inc(v_a_2829_);
v___x_2869_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2827_, v___x_2868_, v_a_2829_, v_a_2830_, v_a_2831_);
v___y_2834_ = v___x_2869_;
goto v___jp_2833_;
}
v___jp_2833_:
{
if (lean_obj_tag(v___y_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
v_a_2835_ = lean_ctor_get(v___y_2834_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___y_2834_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___y_2834_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___y_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___y_2834_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___y_2834_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___y_2834_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___y_2834_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_x_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2870_, v_x_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
return v_res_2877_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = l_Lean_interruptExceptionId;
v___x_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___x_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v_ks_2900_; lean_object* v_vs_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2933_; 
v_ks_2900_ = lean_ctor_get(v_x_2896_, 0);
v_vs_2901_ = lean_ctor_get(v_x_2896_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_x_2896_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2903_ = v_x_2896_;
v_isShared_2904_ = v_isSharedCheck_2933_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_vs_2901_);
lean_inc(v_ks_2900_);
lean_dec(v_x_2896_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2933_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_array_get_size(v_ks_2900_);
v___x_2906_ = lean_nat_dec_lt(v_x_2897_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
lean_dec(v_x_2897_);
v___x_2907_ = lean_array_push(v_ks_2900_, v_x_2898_);
v___x_2908_ = lean_array_push(v_vs_2901_, v_x_2899_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2908_);
lean_ctor_set(v___x_2903_, 0, v___x_2907_);
v___x_2910_ = v___x_2903_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
else
{
lean_object* v_expr_2912_; uint64_t v_configKey_2913_; lean_object* v_k_x27_2914_; lean_object* v_expr_2915_; uint64_t v_configKey_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; uint8_t v___x_2921_; 
v_expr_2912_ = lean_ctor_get(v_x_2898_, 0);
v_configKey_2913_ = lean_ctor_get_uint64(v_x_2898_, sizeof(void*)*1);
v_k_x27_2914_ = lean_array_fget_borrowed(v_ks_2900_, v_x_2897_);
v_expr_2915_ = lean_ctor_get(v_k_x27_2914_, 0);
v_configKey_2916_ = lean_ctor_get_uint64(v_k_x27_2914_, sizeof(void*)*1);
v___x_2917_ = l_Lean_Expr_hash(v_expr_2912_);
v___x_2918_ = lean_uint64_mix_hash(v___x_2917_, v_configKey_2913_);
v___x_2919_ = l_Lean_Expr_hash(v_expr_2915_);
v___x_2920_ = lean_uint64_mix_hash(v___x_2919_, v_configKey_2916_);
v___x_2921_ = lean_uint64_dec_eq(v___x_2918_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2923_; 
if (v_isShared_2904_ == 0)
{
v___x_2923_ = v___x_2903_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_ks_2900_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_vs_2901_);
v___x_2923_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_nat_add(v_x_2897_, v___x_2924_);
lean_dec(v_x_2897_);
v_x_2896_ = v___x_2923_;
v_x_2897_ = v___x_2925_;
goto _start;
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2928_ = lean_array_fset(v_ks_2900_, v_x_2897_, v_x_2898_);
v___x_2929_ = lean_array_fset(v_vs_2901_, v_x_2897_, v_x_2899_);
lean_dec(v_x_2897_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v___x_2929_);
lean_ctor_set(v___x_2903_, 0, v___x_2928_);
v___x_2931_ = v___x_2903_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2934_, lean_object* v_k_2935_, lean_object* v_v_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_n_2934_, v___x_2937_, v_k_2935_, v_v_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2939_, size_t v_x_2940_, size_t v_x_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
lean_object* v_es_2944_; size_t v___x_2945_; size_t v___x_2946_; lean_object* v_j_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_es_2944_ = lean_ctor_get(v_x_2939_, 0);
v___x_2945_ = ((size_t)31ULL);
v___x_2946_ = lean_usize_land(v_x_2940_, v___x_2945_);
v_j_2947_ = lean_usize_to_nat(v___x_2946_);
v___x_2948_ = lean_array_get_size(v_es_2944_);
v___x_2949_ = lean_nat_dec_lt(v_j_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_dec(v_j_2947_);
lean_dec(v_x_2943_);
lean_dec_ref(v_x_2942_);
return v_x_2939_;
}
else
{
lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2996_; 
lean_inc_ref(v_es_2944_);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v_x_2939_, 0);
lean_dec(v_unused_2997_);
v___x_2951_ = v_x_2939_;
v_isShared_2952_ = v_isSharedCheck_2996_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v_x_2939_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2996_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_v_2953_; lean_object* v___x_2954_; lean_object* v_xs_x27_2955_; lean_object* v___y_2957_; 
v_v_2953_ = lean_array_fget(v_es_2944_, v_j_2947_);
v___x_2954_ = lean_box(0);
v_xs_x27_2955_ = lean_array_fset(v_es_2944_, v_j_2947_, v___x_2954_);
switch(lean_obj_tag(v_v_2953_))
{
case 0:
{
lean_object* v_key_2962_; lean_object* v_val_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2981_; 
v_key_2962_ = lean_ctor_get(v_v_2953_, 0);
v_val_2963_ = lean_ctor_get(v_v_2953_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_v_2953_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2965_ = v_v_2953_;
v_isShared_2966_ = v_isSharedCheck_2981_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_val_2963_);
lean_inc(v_key_2962_);
lean_dec(v_v_2953_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2981_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_expr_2967_; uint64_t v_configKey_2968_; lean_object* v_expr_2969_; uint64_t v_configKey_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; uint64_t v___x_2974_; uint8_t v___x_2975_; 
v_expr_2967_ = lean_ctor_get(v_x_2942_, 0);
v_configKey_2968_ = lean_ctor_get_uint64(v_x_2942_, sizeof(void*)*1);
v_expr_2969_ = lean_ctor_get(v_key_2962_, 0);
v_configKey_2970_ = lean_ctor_get_uint64(v_key_2962_, sizeof(void*)*1);
v___x_2971_ = l_Lean_Expr_hash(v_expr_2967_);
v___x_2972_ = lean_uint64_mix_hash(v___x_2971_, v_configKey_2968_);
v___x_2973_ = l_Lean_Expr_hash(v_expr_2969_);
v___x_2974_ = lean_uint64_mix_hash(v___x_2973_, v_configKey_2970_);
v___x_2975_ = lean_uint64_dec_eq(v___x_2972_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_del_object(v___x_2965_);
v___x_2976_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2962_, v_val_2963_, v_x_2942_, v_x_2943_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___y_2957_ = v___x_2977_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2979_; 
lean_dec(v_val_2963_);
lean_dec(v_key_2962_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v_x_2943_);
lean_ctor_set(v___x_2965_, 0, v_x_2942_);
v___x_2979_ = v___x_2965_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_x_2942_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_x_2943_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
v___y_2957_ = v___x_2979_;
goto v___jp_2956_;
}
}
}
}
case 1:
{
lean_object* v_node_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2994_; 
v_node_2982_ = lean_ctor_get(v_v_2953_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_v_2953_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2984_ = v_v_2953_;
v_isShared_2985_ = v_isSharedCheck_2994_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_node_2982_);
lean_dec(v_v_2953_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2994_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
size_t v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2986_ = ((size_t)5ULL);
v___x_2987_ = lean_usize_shift_right(v_x_2940_, v___x_2986_);
v___x_2988_ = ((size_t)1ULL);
v___x_2989_ = lean_usize_add(v_x_2941_, v___x_2988_);
v___x_2990_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2982_, v___x_2987_, v___x_2989_, v_x_2942_, v_x_2943_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2990_);
v___x_2992_ = v___x_2984_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
v___y_2957_ = v___x_2992_;
goto v___jp_2956_;
}
}
}
default: 
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v_x_2942_);
lean_ctor_set(v___x_2995_, 1, v_x_2943_);
v___y_2957_ = v___x_2995_;
goto v___jp_2956_;
}
}
v___jp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_array_fset(v_xs_x27_2955_, v_j_2947_, v___y_2957_);
lean_dec(v_j_2947_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2958_);
v___x_2960_ = v___x_2951_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
else
{
lean_object* v_ks_2998_; lean_object* v_vs_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3017_; 
v_ks_2998_ = lean_ctor_get(v_x_2939_, 0);
v_vs_2999_ = lean_ctor_get(v_x_2939_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3001_ = v_x_2939_;
v_isShared_3002_ = v_isSharedCheck_3017_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_vs_2999_);
lean_inc(v_ks_2998_);
lean_dec(v_x_2939_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3017_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_ks_2998_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_vs_2999_);
v___x_3004_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v_newNode_3005_; size_t v___x_3006_; uint8_t v___x_3007_; 
v_newNode_3005_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3004_, v_x_2942_, v_x_2943_);
v___x_3006_ = ((size_t)7ULL);
v___x_3007_ = lean_usize_dec_le(v___x_3006_, v_x_2941_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3008_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3005_);
v___x_3009_ = lean_unsigned_to_nat(4u);
v___x_3010_ = lean_nat_dec_lt(v___x_3008_, v___x_3009_);
lean_dec(v___x_3008_);
if (v___x_3010_ == 0)
{
lean_object* v_ks_3011_; lean_object* v_vs_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_ks_3011_ = lean_ctor_get(v_newNode_3005_, 0);
lean_inc_ref(v_ks_3011_);
v_vs_3012_ = lean_ctor_get(v_newNode_3005_, 1);
lean_inc_ref(v_vs_3012_);
lean_dec_ref(v_newNode_3005_);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2941_, v_ks_3011_, v_vs_3012_, v___x_3013_, v___x_3014_);
lean_dec_ref(v_vs_3012_);
lean_dec_ref(v_ks_3011_);
return v___x_3015_;
}
else
{
return v_newNode_3005_;
}
}
else
{
return v_newNode_3005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3018_, lean_object* v_keys_3019_, lean_object* v_vals_3020_, lean_object* v_i_3021_, lean_object* v_entries_3022_){
_start:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = lean_array_get_size(v_keys_3019_);
v___x_3024_ = lean_nat_dec_lt(v_i_3021_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec(v_i_3021_);
return v_entries_3022_;
}
else
{
lean_object* v_k_3025_; lean_object* v_expr_3026_; uint64_t v_configKey_3027_; lean_object* v_v_3028_; uint64_t v___x_3029_; uint64_t v___x_3030_; size_t v_h_3031_; size_t v___x_3032_; lean_object* v___x_3033_; size_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; size_t v_h_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v_k_3025_ = lean_array_fget_borrowed(v_keys_3019_, v_i_3021_);
v_expr_3026_ = lean_ctor_get(v_k_3025_, 0);
v_configKey_3027_ = lean_ctor_get_uint64(v_k_3025_, sizeof(void*)*1);
v_v_3028_ = lean_array_fget_borrowed(v_vals_3020_, v_i_3021_);
v___x_3029_ = l_Lean_Expr_hash(v_expr_3026_);
v___x_3030_ = lean_uint64_mix_hash(v___x_3029_, v_configKey_3027_);
v_h_3031_ = lean_uint64_to_usize(v___x_3030_);
v___x_3032_ = ((size_t)5ULL);
v___x_3033_ = lean_unsigned_to_nat(1u);
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_sub(v_depth_3018_, v___x_3034_);
v___x_3036_ = lean_usize_mul(v___x_3032_, v___x_3035_);
v_h_3037_ = lean_usize_shift_right(v_h_3031_, v___x_3036_);
v___x_3038_ = lean_nat_add(v_i_3021_, v___x_3033_);
lean_dec(v_i_3021_);
lean_inc(v_v_3028_);
lean_inc(v_k_3025_);
v___x_3039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3022_, v_h_3037_, v_depth_3018_, v_k_3025_, v_v_3028_);
v_i_3021_ = v___x_3038_;
v_entries_3022_ = v___x_3039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3041_, lean_object* v_keys_3042_, lean_object* v_vals_3043_, lean_object* v_i_3044_, lean_object* v_entries_3045_){
_start:
{
size_t v_depth_boxed_3046_; lean_object* v_res_3047_; 
v_depth_boxed_3046_ = lean_unbox_usize(v_depth_3041_);
lean_dec(v_depth_3041_);
v_res_3047_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3046_, v_keys_3042_, v_vals_3043_, v_i_3044_, v_entries_3045_);
lean_dec_ref(v_vals_3043_);
lean_dec_ref(v_keys_3042_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
size_t v_x_3752__boxed_3053_; size_t v_x_3753__boxed_3054_; lean_object* v_res_3055_; 
v_x_3752__boxed_3053_ = lean_unbox_usize(v_x_3049_);
lean_dec(v_x_3049_);
v_x_3753__boxed_3054_ = lean_unbox_usize(v_x_3050_);
lean_dec(v_x_3050_);
v_res_3055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3048_, v_x_3752__boxed_3053_, v_x_3753__boxed_3054_, v_x_3051_, v_x_3052_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_){
_start:
{
lean_object* v_expr_3059_; uint64_t v_configKey_3060_; uint64_t v___x_3061_; uint64_t v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v_expr_3059_ = lean_ctor_get(v_x_3057_, 0);
v_configKey_3060_ = lean_ctor_get_uint64(v_x_3057_, sizeof(void*)*1);
v___x_3061_ = l_Lean_Expr_hash(v_expr_3059_);
v___x_3062_ = lean_uint64_mix_hash(v___x_3061_, v_configKey_3060_);
v___x_3063_ = lean_uint64_to_usize(v___x_3062_);
v___x_3064_ = ((size_t)1ULL);
v___x_3065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3056_, v___x_3063_, v___x_3064_, v_x_3057_, v_x_3058_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3066_, lean_object* v_vals_3067_, lean_object* v_i_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = lean_array_get_size(v_keys_3066_);
v___x_3071_ = lean_nat_dec_lt(v_i_3068_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
lean_dec(v_i_3068_);
v___x_3072_ = lean_box(0);
return v___x_3072_;
}
else
{
lean_object* v_expr_3073_; uint64_t v_configKey_3074_; lean_object* v_k_x27_3075_; lean_object* v_expr_3076_; uint64_t v_configKey_3077_; uint64_t v___x_3078_; uint64_t v___x_3079_; uint64_t v___x_3080_; uint64_t v___x_3081_; uint8_t v___x_3082_; 
v_expr_3073_ = lean_ctor_get(v_k_3069_, 0);
v_configKey_3074_ = lean_ctor_get_uint64(v_k_3069_, sizeof(void*)*1);
v_k_x27_3075_ = lean_array_fget_borrowed(v_keys_3066_, v_i_3068_);
v_expr_3076_ = lean_ctor_get(v_k_x27_3075_, 0);
v_configKey_3077_ = lean_ctor_get_uint64(v_k_x27_3075_, sizeof(void*)*1);
v___x_3078_ = l_Lean_Expr_hash(v_expr_3073_);
v___x_3079_ = lean_uint64_mix_hash(v___x_3078_, v_configKey_3074_);
v___x_3080_ = l_Lean_Expr_hash(v_expr_3076_);
v___x_3081_ = lean_uint64_mix_hash(v___x_3080_, v_configKey_3077_);
v___x_3082_ = lean_uint64_dec_eq(v___x_3079_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_unsigned_to_nat(1u);
v___x_3084_ = lean_nat_add(v_i_3068_, v___x_3083_);
lean_dec(v_i_3068_);
v_i_3068_ = v___x_3084_;
goto _start;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_array_fget_borrowed(v_vals_3067_, v_i_3068_);
lean_dec(v_i_3068_);
lean_inc(v___x_3086_);
lean_inc(v_k_x27_3075_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_k_x27_3075_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3089_, lean_object* v_vals_3090_, lean_object* v_i_3091_, lean_object* v_k_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3089_, v_vals_3090_, v_i_3091_, v_k_3092_);
lean_dec_ref(v_k_3092_);
lean_dec_ref(v_vals_3090_);
lean_dec_ref(v_keys_3089_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3094_, size_t v_x_3095_, lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_object* v_es_3097_; lean_object* v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; lean_object* v_j_3101_; lean_object* v___x_3102_; 
v_es_3097_ = lean_ctor_get(v_x_3094_, 0);
v___x_3098_ = lean_box(2);
v___x_3099_ = ((size_t)31ULL);
v___x_3100_ = lean_usize_land(v_x_3095_, v___x_3099_);
v_j_3101_ = lean_usize_to_nat(v___x_3100_);
v___x_3102_ = lean_array_get_borrowed(v___x_3098_, v_es_3097_, v_j_3101_);
lean_dec(v_j_3101_);
switch(lean_obj_tag(v___x_3102_))
{
case 0:
{
lean_object* v_key_3103_; lean_object* v_val_3104_; lean_object* v_expr_3105_; uint64_t v_configKey_3106_; lean_object* v_expr_3107_; uint64_t v_configKey_3108_; uint64_t v___x_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint8_t v___x_3113_; 
v_key_3103_ = lean_ctor_get(v___x_3102_, 0);
v_val_3104_ = lean_ctor_get(v___x_3102_, 1);
v_expr_3105_ = lean_ctor_get(v_x_3096_, 0);
v_configKey_3106_ = lean_ctor_get_uint64(v_x_3096_, sizeof(void*)*1);
v_expr_3107_ = lean_ctor_get(v_key_3103_, 0);
v_configKey_3108_ = lean_ctor_get_uint64(v_key_3103_, sizeof(void*)*1);
v___x_3109_ = l_Lean_Expr_hash(v_expr_3105_);
v___x_3110_ = lean_uint64_mix_hash(v___x_3109_, v_configKey_3106_);
v___x_3111_ = l_Lean_Expr_hash(v_expr_3107_);
v___x_3112_ = lean_uint64_mix_hash(v___x_3111_, v_configKey_3108_);
v___x_3113_ = lean_uint64_dec_eq(v___x_3110_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_box(0);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_inc(v_val_3104_);
lean_inc(v_key_3103_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_key_3103_);
lean_ctor_set(v___x_3115_, 1, v_val_3104_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
case 1:
{
lean_object* v_node_3117_; size_t v___x_3118_; size_t v___x_3119_; 
v_node_3117_ = lean_ctor_get(v___x_3102_, 0);
v___x_3118_ = ((size_t)5ULL);
v___x_3119_ = lean_usize_shift_right(v_x_3095_, v___x_3118_);
v_x_3094_ = v_node_3117_;
v_x_3095_ = v___x_3119_;
goto _start;
}
default: 
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_box(0);
return v___x_3121_;
}
}
}
else
{
lean_object* v_ks_3122_; lean_object* v_vs_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_ks_3122_ = lean_ctor_get(v_x_3094_, 0);
v_vs_3123_ = lean_ctor_get(v_x_3094_, 1);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3122_, v_vs_3123_, v___x_3124_, v_x_3096_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_){
_start:
{
size_t v_x_3978__boxed_3129_; lean_object* v_res_3130_; 
v_x_3978__boxed_3129_ = lean_unbox_usize(v_x_3127_);
lean_dec(v_x_3127_);
v_res_3130_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3126_, v_x_3978__boxed_3129_, v_x_3128_);
lean_dec_ref(v_x_3128_);
lean_dec_ref(v_x_3126_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v_expr_3133_; uint64_t v_configKey_3134_; uint64_t v___x_3135_; uint64_t v___x_3136_; size_t v___x_3137_; lean_object* v___x_3138_; 
v_expr_3133_ = lean_ctor_get(v_x_3132_, 0);
v_configKey_3134_ = lean_ctor_get_uint64(v_x_3132_, sizeof(void*)*1);
v___x_3135_ = l_Lean_Expr_hash(v_expr_3133_);
v___x_3136_ = lean_uint64_mix_hash(v___x_3135_, v_configKey_3134_);
v___x_3137_ = lean_uint64_to_usize(v___x_3136_);
v___x_3138_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3131_, v___x_3137_, v_x_3132_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3139_, lean_object* v_x_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3139_, v_x_3140_);
lean_dec_ref(v_x_3140_);
lean_dec_ref(v_x_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(lean_object* v_xs_3142_, lean_object* v_v_3143_, lean_object* v_i_3144_){
_start:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = lean_array_get_size(v_xs_3142_);
v___x_3146_ = lean_nat_dec_lt(v_i_3144_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_i_3144_);
v___x_3147_ = lean_box(0);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; lean_object* v_expr_3149_; uint64_t v_configKey_3150_; lean_object* v_expr_3151_; uint64_t v_configKey_3152_; uint64_t v___x_3153_; uint64_t v___x_3154_; uint64_t v___x_3155_; uint64_t v___x_3156_; uint8_t v___x_3157_; 
v___x_3148_ = lean_array_fget_borrowed(v_xs_3142_, v_i_3144_);
v_expr_3149_ = lean_ctor_get(v___x_3148_, 0);
v_configKey_3150_ = lean_ctor_get_uint64(v___x_3148_, sizeof(void*)*1);
v_expr_3151_ = lean_ctor_get(v_v_3143_, 0);
v_configKey_3152_ = lean_ctor_get_uint64(v_v_3143_, sizeof(void*)*1);
v___x_3153_ = l_Lean_Expr_hash(v_expr_3149_);
v___x_3154_ = lean_uint64_mix_hash(v___x_3153_, v_configKey_3150_);
v___x_3155_ = l_Lean_Expr_hash(v_expr_3151_);
v___x_3156_ = lean_uint64_mix_hash(v___x_3155_, v_configKey_3152_);
v___x_3157_ = lean_uint64_dec_eq(v___x_3154_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_add(v_i_3144_, v___x_3158_);
lean_dec(v_i_3144_);
v_i_3144_ = v___x_3159_;
goto _start;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_i_3144_);
return v___x_3161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11___boxed(lean_object* v_xs_3162_, lean_object* v_v_3163_, lean_object* v_i_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3162_, v_v_3163_, v_i_3164_);
lean_dec_ref(v_v_3163_);
lean_dec_ref(v_xs_3162_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(lean_object* v_xs_3166_, lean_object* v_v_3167_){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3166_, v_v_3167_, v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9___boxed(lean_object* v_xs_3170_, lean_object* v_v_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_xs_3170_, v_v_3171_);
lean_dec_ref(v_v_3171_);
lean_dec_ref(v_xs_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(lean_object* v_x_3173_, size_t v_x_3174_, lean_object* v_x_3175_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
lean_object* v_es_3176_; lean_object* v___x_3177_; size_t v___x_3178_; size_t v___x_3179_; lean_object* v_j_3180_; lean_object* v_entry_3181_; 
v_es_3176_ = lean_ctor_get(v_x_3173_, 0);
v___x_3177_ = lean_box(2);
v___x_3178_ = ((size_t)31ULL);
v___x_3179_ = lean_usize_land(v_x_3174_, v___x_3178_);
v_j_3180_ = lean_usize_to_nat(v___x_3179_);
v_entry_3181_ = lean_array_get(v___x_3177_, v_es_3176_, v_j_3180_);
switch(lean_obj_tag(v_entry_3181_))
{
case 0:
{
lean_object* v_key_3182_; lean_object* v_expr_3183_; uint64_t v_configKey_3184_; lean_object* v_expr_3185_; uint64_t v_configKey_3186_; uint64_t v___x_3187_; uint64_t v___x_3188_; uint64_t v___x_3189_; uint64_t v___x_3190_; uint8_t v___x_3191_; 
v_key_3182_ = lean_ctor_get(v_entry_3181_, 0);
lean_inc(v_key_3182_);
lean_dec_ref_known(v_entry_3181_, 2);
v_expr_3183_ = lean_ctor_get(v_x_3175_, 0);
v_configKey_3184_ = lean_ctor_get_uint64(v_x_3175_, sizeof(void*)*1);
v_expr_3185_ = lean_ctor_get(v_key_3182_, 0);
lean_inc_ref(v_expr_3185_);
v_configKey_3186_ = lean_ctor_get_uint64(v_key_3182_, sizeof(void*)*1);
lean_dec(v_key_3182_);
v___x_3187_ = l_Lean_Expr_hash(v_expr_3183_);
v___x_3188_ = lean_uint64_mix_hash(v___x_3187_, v_configKey_3184_);
v___x_3189_ = l_Lean_Expr_hash(v_expr_3185_);
lean_dec_ref(v_expr_3185_);
v___x_3190_ = lean_uint64_mix_hash(v___x_3189_, v_configKey_3186_);
v___x_3191_ = lean_uint64_dec_eq(v___x_3188_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_dec(v_j_3180_);
return v_x_3173_;
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
lean_inc_ref(v_es_3176_);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v_x_3173_, 0);
lean_dec(v_unused_3200_);
v___x_3193_ = v_x_3173_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_x_3173_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = lean_array_set(v_es_3176_, v_j_3180_, v___x_3177_);
lean_dec(v_j_3180_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
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
case 1:
{
lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3235_; 
lean_inc_ref(v_es_3176_);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v_x_3173_, 0);
lean_dec(v_unused_3236_);
v___x_3202_ = v_x_3173_;
v_isShared_3203_ = v_isSharedCheck_3235_;
goto v_resetjp_3201_;
}
else
{
lean_dec(v_x_3173_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3235_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_node_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3234_; 
v_node_3204_ = lean_ctor_get(v_entry_3181_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_entry_3181_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3206_ = v_entry_3181_;
v_isShared_3207_ = v_isSharedCheck_3234_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_node_3204_);
lean_dec(v_entry_3181_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3234_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
size_t v___x_3208_; lean_object* v_entries_3209_; size_t v___x_3210_; lean_object* v_newNode_3211_; lean_object* v___x_3212_; 
v___x_3208_ = ((size_t)5ULL);
v_entries_3209_ = lean_array_set(v_es_3176_, v_j_3180_, v___x_3177_);
v___x_3210_ = lean_usize_shift_right(v_x_3174_, v___x_3208_);
v_newNode_3211_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_node_3204_, v___x_3210_, v_x_3175_);
lean_inc_ref(v_newNode_3211_);
v___x_3212_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3211_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3214_; 
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v_newNode_3211_);
v___x_3214_ = v___x_3206_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_newNode_3211_);
v___x_3214_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3215_ = lean_array_set(v_entries_3209_, v_j_3180_, v___x_3214_);
lean_dec(v_j_3180_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3215_);
v___x_3217_ = v___x_3202_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
else
{
lean_object* v_val_3220_; lean_object* v_fst_3221_; lean_object* v_snd_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v_newNode_3211_);
lean_del_object(v___x_3206_);
v_val_3220_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___x_3212_, 1);
v_fst_3221_ = lean_ctor_get(v_val_3220_, 0);
v_snd_3222_ = lean_ctor_get(v_val_3220_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_val_3220_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3224_ = v_val_3220_;
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snd_3222_);
lean_inc(v_fst_3221_);
lean_dec(v_val_3220_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_fst_3221_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_snd_3222_);
v___x_3227_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_array_set(v_entries_3209_, v_j_3180_, v___x_3227_);
lean_dec(v_j_3180_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3228_);
v___x_3230_ = v___x_3202_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
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
default: 
{
lean_dec(v_j_3180_);
return v_x_3173_;
}
}
}
else
{
lean_object* v_ks_3237_; lean_object* v_vs_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3252_; 
v_ks_3237_ = lean_ctor_get(v_x_3173_, 0);
v_vs_3238_ = lean_ctor_get(v_x_3173_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3240_ = v_x_3173_;
v_isShared_3241_ = v_isSharedCheck_3252_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_vs_3238_);
lean_inc(v_ks_3237_);
lean_dec(v_x_3173_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3252_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_ks_3237_, v_x_3175_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3244_; 
if (v_isShared_3241_ == 0)
{
v___x_3244_ = v___x_3240_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_ks_3237_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_vs_3238_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
else
{
lean_object* v_val_3246_; lean_object* v_keys_x27_3247_; lean_object* v_vals_x27_3248_; lean_object* v___x_3250_; 
v_val_3246_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_n(v_val_3246_, 2);
lean_dec_ref_known(v___x_3242_, 1);
v_keys_x27_3247_ = l_Array_eraseIdx___redArg(v_ks_3237_, v_val_3246_);
v_vals_x27_3248_ = l_Array_eraseIdx___redArg(v_vs_3238_, v_val_3246_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v_vals_x27_3248_);
lean_ctor_set(v___x_3240_, 0, v_keys_x27_3247_);
v___x_3250_ = v___x_3240_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_keys_x27_3247_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_vals_x27_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg___boxed(lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_){
_start:
{
size_t v_x_4099__boxed_3256_; lean_object* v_res_3257_; 
v_x_4099__boxed_3256_ = lean_unbox_usize(v_x_3254_);
lean_dec(v_x_3254_);
v_res_3257_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3253_, v_x_4099__boxed_3256_, v_x_3255_);
lean_dec_ref(v_x_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
lean_object* v_expr_3260_; uint64_t v_configKey_3261_; uint64_t v___x_3262_; uint64_t v___x_3263_; size_t v_h_3264_; lean_object* v___x_3265_; 
v_expr_3260_ = lean_ctor_get(v_x_3259_, 0);
v_configKey_3261_ = lean_ctor_get_uint64(v_x_3259_, sizeof(void*)*1);
v___x_3262_ = l_Lean_Expr_hash(v_expr_3260_);
v___x_3263_ = lean_uint64_mix_hash(v___x_3262_, v_configKey_3261_);
v_h_3264_ = lean_uint64_to_usize(v___x_3263_);
v___x_3265_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3258_, v_h_3264_, v_x_3259_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg___boxed(lean_object* v_x_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3266_, v_x_3267_);
lean_dec_ref(v_x_3267_);
return v_res_3268_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
switch(lean_obj_tag(v_e_3272_))
{
case 0:
{
lean_object* v_deBruijnIndex_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_deBruijnIndex_3310_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_deBruijnIndex_3310_);
lean_dec_ref_known(v_e_3272_, 1);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3312_ = l_Lean_mkBVar(v_deBruijnIndex_3310_);
v___x_3313_ = l_Lean_MessageData_ofExpr(v___x_3312_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3311_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3314_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3315_;
}
case 1:
{
lean_object* v_fvarId_3316_; lean_object* v___x_3317_; 
v_fvarId_3316_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_fvarId_3316_);
lean_dec_ref_known(v_e_3272_, 1);
v___x_3317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3316_, v_a_3273_, v_a_3275_, v_a_3276_);
return v___x_3317_;
}
case 2:
{
lean_object* v_mvarId_3318_; lean_object* v___x_3319_; 
v_mvarId_3318_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_mvarId_3318_);
lean_dec_ref_known(v_e_3272_, 1);
v___x_3319_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3318_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3319_;
}
case 3:
{
lean_object* v_u_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_u_3320_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_u_3320_);
lean_dec_ref_known(v_e_3272_, 1);
v___x_3321_ = l_Lean_Level_succ___override(v_u_3320_);
v___x_3322_ = l_Lean_mkSort(v___x_3321_);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
case 4:
{
lean_object* v_declName_3324_; lean_object* v_us_3325_; 
v_declName_3324_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_declName_3324_);
v_us_3325_ = lean_ctor_get(v_e_3272_, 1);
lean_inc(v_us_3325_);
if (lean_obj_tag(v_us_3325_) == 0)
{
lean_object* v___x_3342_; 
lean_dec_ref_known(v_e_3272_, 2);
v___x_3342_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3324_, v_us_3325_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3342_;
}
else
{
uint8_t v_cacheInferType_3343_; 
v_cacheInferType_3343_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3343_ == 0)
{
lean_dec_ref_known(v_e_3272_, 2);
goto v___jp_3326_;
}
else
{
uint8_t v___x_3344_; 
v___x_3344_ = l_Lean_Expr_hasMVar(v_e_3272_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3451_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3451_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3451_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3405_; lean_object* v_cache_3406_; lean_object* v_inferType_3407_; lean_object* v___x_3408_; 
v___x_3405_ = lean_st_ref_get(v_a_3274_);
v_cache_3406_ = lean_ctor_get(v___x_3405_, 1);
lean_inc_ref(v_cache_3406_);
lean_dec(v___x_3405_);
v_inferType_3407_ = lean_ctor_get(v_cache_3406_, 0);
lean_inc_ref(v_inferType_3407_);
lean_dec_ref(v_cache_3406_);
v___x_3408_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3407_, v_a_3346_);
if (lean_obj_tag(v___x_3408_) == 1)
{
lean_object* v_val_3409_; lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v_expr_3412_; uint64_t v_configKey_3413_; lean_object* v_expr_3414_; uint64_t v_configKey_3415_; uint8_t v___x_3416_; 
v_val_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_val_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v_fst_3410_ = lean_ctor_get(v_val_3409_, 0);
lean_inc(v_fst_3410_);
v_snd_3411_ = lean_ctor_get(v_val_3409_, 1);
lean_inc(v_snd_3411_);
lean_dec(v_val_3409_);
v_expr_3412_ = lean_ctor_get(v_a_3346_, 0);
v_configKey_3413_ = lean_ctor_get_uint64(v_a_3346_, sizeof(void*)*1);
v_expr_3414_ = lean_ctor_get(v_fst_3410_, 0);
lean_inc_ref(v_expr_3414_);
v_configKey_3415_ = lean_ctor_get_uint64(v_fst_3410_, sizeof(void*)*1);
lean_dec(v_fst_3410_);
v___x_3416_ = lean_uint64_dec_eq(v_configKey_3413_, v_configKey_3415_);
if (v___x_3416_ == 0)
{
lean_dec_ref(v_expr_3414_);
lean_dec(v_snd_3411_);
lean_dec_ref(v_inferType_3407_);
lean_del_object(v___x_3348_);
goto v___jp_3391_;
}
else
{
size_t v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = ((size_t)64ULL);
v___x_3418_ = lean_expr_equal_budgeted(v_expr_3412_, v_expr_3414_, v___x_3417_);
lean_dec_ref(v_expr_3414_);
switch(v___x_3418_)
{
case 0:
{
lean_dec(v_snd_3411_);
lean_dec_ref(v_inferType_3407_);
lean_del_object(v___x_3348_);
goto v___jp_3391_;
}
case 1:
{
lean_object* v___x_3420_; 
lean_dec_ref(v_inferType_3407_);
lean_dec(v_a_3346_);
lean_dec(v_us_3325_);
lean_dec(v_declName_3324_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_snd_3411_);
v___x_3420_ = v___x_3348_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_snd_3411_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
default: 
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_cache_3424_; lean_object* v_mctx_3425_; lean_object* v_zetaDeltaFVarIds_3426_; lean_object* v_postponed_3427_; lean_object* v_diag_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_snd_3411_);
lean_del_object(v___x_3348_);
v___x_3422_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3407_, v_a_3346_);
v___x_3423_ = lean_st_ref_take(v_a_3274_);
v_cache_3424_ = lean_ctor_get(v___x_3423_, 1);
v_mctx_3425_ = lean_ctor_get(v___x_3423_, 0);
v_zetaDeltaFVarIds_3426_ = lean_ctor_get(v___x_3423_, 2);
v_postponed_3427_ = lean_ctor_get(v___x_3423_, 3);
v_diag_3428_ = lean_ctor_get(v___x_3423_, 4);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3430_ = v___x_3423_;
v_isShared_3431_ = v_isSharedCheck_3450_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_diag_3428_);
lean_inc(v_postponed_3427_);
lean_inc(v_zetaDeltaFVarIds_3426_);
lean_inc(v_cache_3424_);
lean_inc(v_mctx_3425_);
lean_dec(v___x_3423_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3450_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_funInfo_3432_; lean_object* v_synthInstance_3433_; lean_object* v_whnf_3434_; lean_object* v_defEqTrans_3435_; lean_object* v_defEqPerm_3436_; lean_object* v_unfold_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3448_; 
v_funInfo_3432_ = lean_ctor_get(v_cache_3424_, 1);
v_synthInstance_3433_ = lean_ctor_get(v_cache_3424_, 2);
v_whnf_3434_ = lean_ctor_get(v_cache_3424_, 3);
v_defEqTrans_3435_ = lean_ctor_get(v_cache_3424_, 4);
v_defEqPerm_3436_ = lean_ctor_get(v_cache_3424_, 5);
v_unfold_3437_ = lean_ctor_get(v_cache_3424_, 6);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_cache_3424_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v_cache_3424_, 0);
lean_dec(v_unused_3449_);
v___x_3439_ = v_cache_3424_;
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_unfold_3437_);
lean_inc(v_defEqPerm_3436_);
lean_inc(v_defEqTrans_3435_);
lean_inc(v_whnf_3434_);
lean_inc(v_synthInstance_3433_);
lean_inc(v_funInfo_3432_);
lean_dec(v_cache_3424_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3422_);
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_funInfo_3432_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_synthInstance_3433_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_whnf_3434_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_defEqTrans_3435_);
lean_ctor_set(v_reuseFailAlloc_3447_, 5, v_defEqPerm_3436_);
lean_ctor_set(v_reuseFailAlloc_3447_, 6, v_unfold_3437_);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3442_);
v___x_3444_ = v___x_3430_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_mctx_3425_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_zetaDeltaFVarIds_3426_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_postponed_3427_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_diag_3428_);
v___x_3444_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_st_ref_put(v_a_3274_, v___x_3444_);
goto v___jp_3391_;
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
lean_dec(v___x_3408_);
lean_dec_ref(v_inferType_3407_);
lean_del_object(v___x_3348_);
goto v___jp_3391_;
}
v___jp_3350_:
{
lean_object* v___x_3351_; 
v___x_3351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3324_, v_us_3325_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; uint8_t v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v___x_3353_ = l_Lean_Expr_hasMVar(v_a_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3389_; 
lean_inc(v_a_3352_);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v___x_3351_, 0);
lean_dec(v_unused_3390_);
v___x_3355_ = v___x_3351_;
v_isShared_3356_ = v_isSharedCheck_3389_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v___x_3351_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3389_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v_cache_3358_; lean_object* v_mctx_3359_; lean_object* v_zetaDeltaFVarIds_3360_; lean_object* v_postponed_3361_; lean_object* v_diag_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3388_; 
v___x_3357_ = lean_st_ref_take(v_a_3274_);
v_cache_3358_ = lean_ctor_get(v___x_3357_, 1);
v_mctx_3359_ = lean_ctor_get(v___x_3357_, 0);
v_zetaDeltaFVarIds_3360_ = lean_ctor_get(v___x_3357_, 2);
v_postponed_3361_ = lean_ctor_get(v___x_3357_, 3);
v_diag_3362_ = lean_ctor_get(v___x_3357_, 4);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3364_ = v___x_3357_;
v_isShared_3365_ = v_isSharedCheck_3388_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_diag_3362_);
lean_inc(v_postponed_3361_);
lean_inc(v_zetaDeltaFVarIds_3360_);
lean_inc(v_cache_3358_);
lean_inc(v_mctx_3359_);
lean_dec(v___x_3357_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3388_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_inferType_3366_; lean_object* v_funInfo_3367_; lean_object* v_synthInstance_3368_; lean_object* v_whnf_3369_; lean_object* v_defEqTrans_3370_; lean_object* v_defEqPerm_3371_; lean_object* v_unfold_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3387_; 
v_inferType_3366_ = lean_ctor_get(v_cache_3358_, 0);
v_funInfo_3367_ = lean_ctor_get(v_cache_3358_, 1);
v_synthInstance_3368_ = lean_ctor_get(v_cache_3358_, 2);
v_whnf_3369_ = lean_ctor_get(v_cache_3358_, 3);
v_defEqTrans_3370_ = lean_ctor_get(v_cache_3358_, 4);
v_defEqPerm_3371_ = lean_ctor_get(v_cache_3358_, 5);
v_unfold_3372_ = lean_ctor_get(v_cache_3358_, 6);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_cache_3358_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3374_ = v_cache_3358_;
v_isShared_3375_ = v_isSharedCheck_3387_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_unfold_3372_);
lean_inc(v_defEqPerm_3371_);
lean_inc(v_defEqTrans_3370_);
lean_inc(v_whnf_3369_);
lean_inc(v_synthInstance_3368_);
lean_inc(v_funInfo_3367_);
lean_inc(v_inferType_3366_);
lean_dec(v_cache_3358_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3387_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_inc(v_a_3352_);
v___x_3376_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3366_, v_a_3346_, v_a_3352_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_funInfo_3367_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_synthInstance_3368_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_whnf_3369_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_defEqTrans_3370_);
lean_ctor_set(v_reuseFailAlloc_3386_, 5, v_defEqPerm_3371_);
lean_ctor_set(v_reuseFailAlloc_3386_, 6, v_unfold_3372_);
v___x_3378_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v___x_3378_);
v___x_3380_ = v___x_3364_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_mctx_3359_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_zetaDeltaFVarIds_3360_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_postponed_3361_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_diag_3362_);
v___x_3380_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_st_ref_put(v_a_3274_, v___x_3380_);
if (v_isShared_3356_ == 0)
{
v___x_3383_ = v___x_3355_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3352_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3346_);
return v___x_3351_;
}
}
else
{
lean_dec(v_a_3346_);
return v___x_3351_;
}
}
v___jp_3391_:
{
lean_object* v_toCold_3392_; lean_object* v_cancelTk_x3f_3393_; 
v_toCold_3392_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3393_ = lean_ctor_get(v_toCold_3392_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3393_) == 1)
{
lean_object* v_val_3394_; uint8_t v___x_3395_; 
v_val_3394_ = lean_ctor_get(v_cancelTk_x3f_3393_, 0);
v___x_3395_ = l_IO_CancelToken_isSet(v_val_3394_);
if (v___x_3395_ == 0)
{
goto v___jp_3350_;
}
else
{
lean_object* v___x_3396_; lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_a_3346_);
lean_dec(v_us_3325_);
lean_dec(v_declName_3324_);
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
goto v___jp_3350_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v_us_3325_);
lean_dec(v_declName_3324_);
v_a_3452_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3345_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3345_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3272_, 2);
goto v___jp_3326_;
}
}
}
v___jp_3326_:
{
lean_object* v_toCold_3327_; lean_object* v_cancelTk_x3f_3328_; 
v_toCold_3327_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3328_ = lean_ctor_get(v_toCold_3327_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3328_) == 1)
{
lean_object* v_val_3329_; uint8_t v___x_3330_; 
v_val_3329_ = lean_ctor_get(v_cancelTk_x3f_3328_, 0);
v___x_3330_ = l_IO_CancelToken_isSet(v_val_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3324_, v_us_3325_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_us_3325_);
lean_dec(v_declName_3324_);
v___x_3332_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v___x_3341_; 
v___x_3341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3324_, v_us_3325_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3341_;
}
}
}
case 5:
{
lean_object* v_fn_3460_; uint8_t v_cacheInferType_3461_; lean_object* v_nargs_3462_; lean_object* v___x_3463_; lean_object* v_dummy_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_fn_3460_ = lean_ctor_get(v_e_3272_, 0);
v_cacheInferType_3461_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7 + 3);
v_nargs_3462_ = l_Lean_Expr_getAppNumArgs(v_e_3272_);
v___x_3463_ = l_Lean_Expr_getAppFn(v_fn_3460_);
v_dummy_3464_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3462_);
v___x_3465_ = lean_mk_array(v_nargs_3462_, v_dummy_3464_);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_sub(v_nargs_3462_, v___x_3466_);
lean_dec(v_nargs_3462_);
lean_inc_ref(v_e_3272_);
v___x_3468_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3272_, v___x_3465_, v___x_3467_);
if (v_cacheInferType_3461_ == 0)
{
lean_dec_ref_known(v_e_3272_, 2);
goto v___jp_3469_;
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = l_Lean_Expr_hasMVar(v_e_3272_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3592_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3592_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3592_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3546_; lean_object* v_cache_3547_; lean_object* v_inferType_3548_; lean_object* v___x_3549_; 
v___x_3546_ = lean_st_ref_get(v_a_3274_);
v_cache_3547_ = lean_ctor_get(v___x_3546_, 1);
lean_inc_ref(v_cache_3547_);
lean_dec(v___x_3546_);
v_inferType_3548_ = lean_ctor_get(v_cache_3547_, 0);
lean_inc_ref(v_inferType_3548_);
lean_dec_ref(v_cache_3547_);
v___x_3549_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3548_, v_a_3487_);
if (lean_obj_tag(v___x_3549_) == 1)
{
lean_object* v_val_3550_; lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v_expr_3553_; uint64_t v_configKey_3554_; lean_object* v_expr_3555_; uint64_t v_configKey_3556_; uint8_t v___x_3557_; 
v_val_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_val_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v_fst_3551_ = lean_ctor_get(v_val_3550_, 0);
lean_inc(v_fst_3551_);
v_snd_3552_ = lean_ctor_get(v_val_3550_, 1);
lean_inc(v_snd_3552_);
lean_dec(v_val_3550_);
v_expr_3553_ = lean_ctor_get(v_a_3487_, 0);
v_configKey_3554_ = lean_ctor_get_uint64(v_a_3487_, sizeof(void*)*1);
v_expr_3555_ = lean_ctor_get(v_fst_3551_, 0);
lean_inc_ref(v_expr_3555_);
v_configKey_3556_ = lean_ctor_get_uint64(v_fst_3551_, sizeof(void*)*1);
lean_dec(v_fst_3551_);
v___x_3557_ = lean_uint64_dec_eq(v_configKey_3554_, v_configKey_3556_);
if (v___x_3557_ == 0)
{
lean_dec_ref(v_expr_3555_);
lean_dec(v_snd_3552_);
lean_dec_ref(v_inferType_3548_);
lean_del_object(v___x_3489_);
goto v___jp_3532_;
}
else
{
size_t v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = ((size_t)64ULL);
v___x_3559_ = lean_expr_equal_budgeted(v_expr_3553_, v_expr_3555_, v___x_3558_);
lean_dec_ref(v_expr_3555_);
switch(v___x_3559_)
{
case 0:
{
lean_dec(v_snd_3552_);
lean_dec_ref(v_inferType_3548_);
lean_del_object(v___x_3489_);
goto v___jp_3532_;
}
case 1:
{
lean_object* v___x_3561_; 
lean_dec_ref(v_inferType_3548_);
lean_dec(v_a_3487_);
lean_dec_ref(v___x_3468_);
lean_dec_ref(v___x_3463_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v_snd_3552_);
v___x_3561_ = v___x_3489_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_snd_3552_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
default: 
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_cache_3565_; lean_object* v_mctx_3566_; lean_object* v_zetaDeltaFVarIds_3567_; lean_object* v_postponed_3568_; lean_object* v_diag_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_snd_3552_);
lean_del_object(v___x_3489_);
v___x_3563_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3548_, v_a_3487_);
v___x_3564_ = lean_st_ref_take(v_a_3274_);
v_cache_3565_ = lean_ctor_get(v___x_3564_, 1);
v_mctx_3566_ = lean_ctor_get(v___x_3564_, 0);
v_zetaDeltaFVarIds_3567_ = lean_ctor_get(v___x_3564_, 2);
v_postponed_3568_ = lean_ctor_get(v___x_3564_, 3);
v_diag_3569_ = lean_ctor_get(v___x_3564_, 4);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3571_ = v___x_3564_;
v_isShared_3572_ = v_isSharedCheck_3591_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_diag_3569_);
lean_inc(v_postponed_3568_);
lean_inc(v_zetaDeltaFVarIds_3567_);
lean_inc(v_cache_3565_);
lean_inc(v_mctx_3566_);
lean_dec(v___x_3564_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3591_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_funInfo_3573_; lean_object* v_synthInstance_3574_; lean_object* v_whnf_3575_; lean_object* v_defEqTrans_3576_; lean_object* v_defEqPerm_3577_; lean_object* v_unfold_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3589_; 
v_funInfo_3573_ = lean_ctor_get(v_cache_3565_, 1);
v_synthInstance_3574_ = lean_ctor_get(v_cache_3565_, 2);
v_whnf_3575_ = lean_ctor_get(v_cache_3565_, 3);
v_defEqTrans_3576_ = lean_ctor_get(v_cache_3565_, 4);
v_defEqPerm_3577_ = lean_ctor_get(v_cache_3565_, 5);
v_unfold_3578_ = lean_ctor_get(v_cache_3565_, 6);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_cache_3565_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_cache_3565_, 0);
lean_dec(v_unused_3590_);
v___x_3580_ = v_cache_3565_;
v_isShared_3581_ = v_isSharedCheck_3589_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_unfold_3578_);
lean_inc(v_defEqPerm_3577_);
lean_inc(v_defEqTrans_3576_);
lean_inc(v_whnf_3575_);
lean_inc(v_synthInstance_3574_);
lean_inc(v_funInfo_3573_);
lean_dec(v_cache_3565_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3589_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3563_);
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_funInfo_3573_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_synthInstance_3574_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_whnf_3575_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_defEqTrans_3576_);
lean_ctor_set(v_reuseFailAlloc_3588_, 5, v_defEqPerm_3577_);
lean_ctor_set(v_reuseFailAlloc_3588_, 6, v_unfold_3578_);
v___x_3583_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3583_);
v___x_3585_ = v___x_3571_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_mctx_3566_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_zetaDeltaFVarIds_3567_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_postponed_3568_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_diag_3569_);
v___x_3585_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_st_ref_put(v_a_3274_, v___x_3585_);
goto v___jp_3532_;
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
lean_dec(v___x_3549_);
lean_dec_ref(v_inferType_3548_);
lean_del_object(v___x_3489_);
goto v___jp_3532_;
}
v___jp_3491_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3463_, v___x_3468_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec_ref(v___x_3468_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; uint8_t v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v___x_3494_ = l_Lean_Expr_hasMVar(v_a_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3530_; 
lean_inc(v_a_3493_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v___x_3492_, 0);
lean_dec(v_unused_3531_);
v___x_3496_ = v___x_3492_;
v_isShared_3497_ = v_isSharedCheck_3530_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3530_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v_cache_3499_; lean_object* v_mctx_3500_; lean_object* v_zetaDeltaFVarIds_3501_; lean_object* v_postponed_3502_; lean_object* v_diag_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3529_; 
v___x_3498_ = lean_st_ref_take(v_a_3274_);
v_cache_3499_ = lean_ctor_get(v___x_3498_, 1);
v_mctx_3500_ = lean_ctor_get(v___x_3498_, 0);
v_zetaDeltaFVarIds_3501_ = lean_ctor_get(v___x_3498_, 2);
v_postponed_3502_ = lean_ctor_get(v___x_3498_, 3);
v_diag_3503_ = lean_ctor_get(v___x_3498_, 4);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3505_ = v___x_3498_;
v_isShared_3506_ = v_isSharedCheck_3529_;
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
v_isShared_3506_ = v_isSharedCheck_3529_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_inferType_3507_; lean_object* v_funInfo_3508_; lean_object* v_synthInstance_3509_; lean_object* v_whnf_3510_; lean_object* v_defEqTrans_3511_; lean_object* v_defEqPerm_3512_; lean_object* v_unfold_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3528_; 
v_inferType_3507_ = lean_ctor_get(v_cache_3499_, 0);
v_funInfo_3508_ = lean_ctor_get(v_cache_3499_, 1);
v_synthInstance_3509_ = lean_ctor_get(v_cache_3499_, 2);
v_whnf_3510_ = lean_ctor_get(v_cache_3499_, 3);
v_defEqTrans_3511_ = lean_ctor_get(v_cache_3499_, 4);
v_defEqPerm_3512_ = lean_ctor_get(v_cache_3499_, 5);
v_unfold_3513_ = lean_ctor_get(v_cache_3499_, 6);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_cache_3499_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3515_ = v_cache_3499_;
v_isShared_3516_ = v_isSharedCheck_3528_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_unfold_3513_);
lean_inc(v_defEqPerm_3512_);
lean_inc(v_defEqTrans_3511_);
lean_inc(v_whnf_3510_);
lean_inc(v_synthInstance_3509_);
lean_inc(v_funInfo_3508_);
lean_inc(v_inferType_3507_);
lean_dec(v_cache_3499_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3528_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_inc(v_a_3493_);
v___x_3517_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3507_, v_a_3487_, v_a_3493_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3517_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_funInfo_3508_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_synthInstance_3509_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_whnf_3510_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_defEqTrans_3511_);
lean_ctor_set(v_reuseFailAlloc_3527_, 5, v_defEqPerm_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 6, v_unfold_3513_);
v___x_3519_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3519_);
v___x_3521_ = v___x_3505_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_mctx_3500_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_zetaDeltaFVarIds_3501_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_postponed_3502_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_diag_3503_);
v___x_3521_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3522_ = lean_st_ref_put(v_a_3274_, v___x_3521_);
if (v_isShared_3497_ == 0)
{
v___x_3524_ = v___x_3496_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3493_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
}
else
{
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
v___jp_3532_:
{
lean_object* v_toCold_3533_; lean_object* v_cancelTk_x3f_3534_; 
v_toCold_3533_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3534_ = lean_ctor_get(v_toCold_3533_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3534_) == 1)
{
lean_object* v_val_3535_; uint8_t v___x_3536_; 
v_val_3535_ = lean_ctor_get(v_cancelTk_x3f_3534_, 0);
v___x_3536_ = l_IO_CancelToken_isSet(v_val_3535_);
if (v___x_3536_ == 0)
{
goto v___jp_3491_;
}
else
{
lean_object* v___x_3537_; lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3487_);
lean_dec_ref(v___x_3468_);
lean_dec_ref(v___x_3463_);
v___x_3537_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
goto v___jp_3491_;
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec_ref(v___x_3468_);
lean_dec_ref(v___x_3463_);
v_a_3593_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3486_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3486_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3272_, 2);
goto v___jp_3469_;
}
}
v___jp_3469_:
{
lean_object* v_toCold_3470_; lean_object* v_cancelTk_x3f_3471_; 
v_toCold_3470_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3471_ = lean_ctor_get(v_toCold_3470_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3471_) == 1)
{
lean_object* v_val_3472_; uint8_t v___x_3473_; 
v_val_3472_ = lean_ctor_get(v_cancelTk_x3f_3471_, 0);
v___x_3473_ = l_IO_CancelToken_isSet(v_val_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
v___x_3474_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3463_, v___x_3468_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec_ref(v___x_3468_);
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v___x_3468_);
lean_dec_ref(v___x_3463_);
v___x_3475_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
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
lean_object* v___x_3484_; 
v___x_3484_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3463_, v___x_3468_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec_ref(v___x_3468_);
return v___x_3484_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3601_; 
v_cacheInferType_3601_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3601_ == 0)
{
goto v___jp_3278_;
}
else
{
uint8_t v___x_3602_; 
v___x_3602_ = l_Lean_Expr_hasMVar(v_e_3272_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; 
lean_inc_ref(v_e_3272_);
v___x_3603_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3709_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3606_ = v___x_3603_;
v_isShared_3607_ = v_isSharedCheck_3709_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3603_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3709_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3663_; lean_object* v_cache_3664_; lean_object* v_inferType_3665_; lean_object* v___x_3666_; 
v___x_3663_ = lean_st_ref_get(v_a_3274_);
v_cache_3664_ = lean_ctor_get(v___x_3663_, 1);
lean_inc_ref(v_cache_3664_);
lean_dec(v___x_3663_);
v_inferType_3665_ = lean_ctor_get(v_cache_3664_, 0);
lean_inc_ref(v_inferType_3665_);
lean_dec_ref(v_cache_3664_);
v___x_3666_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3665_, v_a_3604_);
if (lean_obj_tag(v___x_3666_) == 1)
{
lean_object* v_val_3667_; lean_object* v_fst_3668_; lean_object* v_snd_3669_; lean_object* v_expr_3670_; uint64_t v_configKey_3671_; lean_object* v_expr_3672_; uint64_t v_configKey_3673_; uint8_t v___x_3674_; 
v_val_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_val_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v_fst_3668_ = lean_ctor_get(v_val_3667_, 0);
lean_inc(v_fst_3668_);
v_snd_3669_ = lean_ctor_get(v_val_3667_, 1);
lean_inc(v_snd_3669_);
lean_dec(v_val_3667_);
v_expr_3670_ = lean_ctor_get(v_a_3604_, 0);
v_configKey_3671_ = lean_ctor_get_uint64(v_a_3604_, sizeof(void*)*1);
v_expr_3672_ = lean_ctor_get(v_fst_3668_, 0);
lean_inc_ref(v_expr_3672_);
v_configKey_3673_ = lean_ctor_get_uint64(v_fst_3668_, sizeof(void*)*1);
lean_dec(v_fst_3668_);
v___x_3674_ = lean_uint64_dec_eq(v_configKey_3671_, v_configKey_3673_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_expr_3672_);
lean_dec(v_snd_3669_);
lean_dec_ref(v_inferType_3665_);
lean_del_object(v___x_3606_);
goto v___jp_3649_;
}
else
{
size_t v___x_3675_; uint8_t v___x_3676_; 
v___x_3675_ = ((size_t)64ULL);
v___x_3676_ = lean_expr_equal_budgeted(v_expr_3670_, v_expr_3672_, v___x_3675_);
lean_dec_ref(v_expr_3672_);
switch(v___x_3676_)
{
case 0:
{
lean_dec(v_snd_3669_);
lean_dec_ref(v_inferType_3665_);
lean_del_object(v___x_3606_);
goto v___jp_3649_;
}
case 1:
{
lean_object* v___x_3678_; 
lean_dec_ref(v_inferType_3665_);
lean_dec(v_a_3604_);
lean_dec_ref_known(v_e_3272_, 3);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v_snd_3669_);
v___x_3678_ = v___x_3606_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_snd_3669_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
default: 
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_cache_3682_; lean_object* v_mctx_3683_; lean_object* v_zetaDeltaFVarIds_3684_; lean_object* v_postponed_3685_; lean_object* v_diag_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_snd_3669_);
lean_del_object(v___x_3606_);
v___x_3680_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3665_, v_a_3604_);
v___x_3681_ = lean_st_ref_take(v_a_3274_);
v_cache_3682_ = lean_ctor_get(v___x_3681_, 1);
v_mctx_3683_ = lean_ctor_get(v___x_3681_, 0);
v_zetaDeltaFVarIds_3684_ = lean_ctor_get(v___x_3681_, 2);
v_postponed_3685_ = lean_ctor_get(v___x_3681_, 3);
v_diag_3686_ = lean_ctor_get(v___x_3681_, 4);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3688_ = v___x_3681_;
v_isShared_3689_ = v_isSharedCheck_3708_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_diag_3686_);
lean_inc(v_postponed_3685_);
lean_inc(v_zetaDeltaFVarIds_3684_);
lean_inc(v_cache_3682_);
lean_inc(v_mctx_3683_);
lean_dec(v___x_3681_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3708_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v_funInfo_3690_; lean_object* v_synthInstance_3691_; lean_object* v_whnf_3692_; lean_object* v_defEqTrans_3693_; lean_object* v_defEqPerm_3694_; lean_object* v_unfold_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3706_; 
v_funInfo_3690_ = lean_ctor_get(v_cache_3682_, 1);
v_synthInstance_3691_ = lean_ctor_get(v_cache_3682_, 2);
v_whnf_3692_ = lean_ctor_get(v_cache_3682_, 3);
v_defEqTrans_3693_ = lean_ctor_get(v_cache_3682_, 4);
v_defEqPerm_3694_ = lean_ctor_get(v_cache_3682_, 5);
v_unfold_3695_ = lean_ctor_get(v_cache_3682_, 6);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_cache_3682_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v_cache_3682_, 0);
lean_dec(v_unused_3707_);
v___x_3697_ = v_cache_3682_;
v_isShared_3698_ = v_isSharedCheck_3706_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_unfold_3695_);
lean_inc(v_defEqPerm_3694_);
lean_inc(v_defEqTrans_3693_);
lean_inc(v_whnf_3692_);
lean_inc(v_synthInstance_3691_);
lean_inc(v_funInfo_3690_);
lean_dec(v_cache_3682_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3706_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3680_);
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_funInfo_3690_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_synthInstance_3691_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_whnf_3692_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_defEqTrans_3693_);
lean_ctor_set(v_reuseFailAlloc_3705_, 5, v_defEqPerm_3694_);
lean_ctor_set(v_reuseFailAlloc_3705_, 6, v_unfold_3695_);
v___x_3700_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 1, v___x_3700_);
v___x_3702_ = v___x_3688_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_mctx_3683_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_zetaDeltaFVarIds_3684_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_postponed_3685_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_diag_3686_);
v___x_3702_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_st_ref_put(v_a_3274_, v___x_3702_);
goto v___jp_3649_;
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
lean_dec(v___x_3666_);
lean_dec_ref(v_inferType_3665_);
lean_del_object(v___x_3606_);
goto v___jp_3649_;
}
v___jp_3608_:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; uint8_t v___x_3611_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v___x_3611_ = l_Lean_Expr_hasMVar(v_a_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3647_; 
lean_inc(v_a_3610_);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v___x_3609_, 0);
lean_dec(v_unused_3648_);
v___x_3613_ = v___x_3609_;
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
else
{
lean_dec(v___x_3609_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3647_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v_cache_3616_; lean_object* v_mctx_3617_; lean_object* v_zetaDeltaFVarIds_3618_; lean_object* v_postponed_3619_; lean_object* v_diag_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3646_; 
v___x_3615_ = lean_st_ref_take(v_a_3274_);
v_cache_3616_ = lean_ctor_get(v___x_3615_, 1);
v_mctx_3617_ = lean_ctor_get(v___x_3615_, 0);
v_zetaDeltaFVarIds_3618_ = lean_ctor_get(v___x_3615_, 2);
v_postponed_3619_ = lean_ctor_get(v___x_3615_, 3);
v_diag_3620_ = lean_ctor_get(v___x_3615_, 4);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3622_ = v___x_3615_;
v_isShared_3623_ = v_isSharedCheck_3646_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_diag_3620_);
lean_inc(v_postponed_3619_);
lean_inc(v_zetaDeltaFVarIds_3618_);
lean_inc(v_cache_3616_);
lean_inc(v_mctx_3617_);
lean_dec(v___x_3615_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3646_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v_inferType_3624_; lean_object* v_funInfo_3625_; lean_object* v_synthInstance_3626_; lean_object* v_whnf_3627_; lean_object* v_defEqTrans_3628_; lean_object* v_defEqPerm_3629_; lean_object* v_unfold_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3645_; 
v_inferType_3624_ = lean_ctor_get(v_cache_3616_, 0);
v_funInfo_3625_ = lean_ctor_get(v_cache_3616_, 1);
v_synthInstance_3626_ = lean_ctor_get(v_cache_3616_, 2);
v_whnf_3627_ = lean_ctor_get(v_cache_3616_, 3);
v_defEqTrans_3628_ = lean_ctor_get(v_cache_3616_, 4);
v_defEqPerm_3629_ = lean_ctor_get(v_cache_3616_, 5);
v_unfold_3630_ = lean_ctor_get(v_cache_3616_, 6);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_cache_3616_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3632_ = v_cache_3616_;
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_unfold_3630_);
lean_inc(v_defEqPerm_3629_);
lean_inc(v_defEqTrans_3628_);
lean_inc(v_whnf_3627_);
lean_inc(v_synthInstance_3626_);
lean_inc(v_funInfo_3625_);
lean_inc(v_inferType_3624_);
lean_dec(v_cache_3616_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3645_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_inc(v_a_3610_);
v___x_3634_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3624_, v_a_3604_, v_a_3610_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_funInfo_3625_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_synthInstance_3626_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_whnf_3627_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_defEqTrans_3628_);
lean_ctor_set(v_reuseFailAlloc_3644_, 5, v_defEqPerm_3629_);
lean_ctor_set(v_reuseFailAlloc_3644_, 6, v_unfold_3630_);
v___x_3636_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 1, v___x_3636_);
v___x_3638_ = v___x_3622_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_mctx_3617_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_zetaDeltaFVarIds_3618_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_postponed_3619_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_diag_3620_);
v___x_3638_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_st_ref_put(v_a_3274_, v___x_3638_);
if (v_isShared_3614_ == 0)
{
v___x_3641_ = v___x_3613_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3610_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3604_);
return v___x_3609_;
}
}
else
{
lean_dec(v_a_3604_);
return v___x_3609_;
}
}
v___jp_3649_:
{
lean_object* v_toCold_3650_; lean_object* v_cancelTk_x3f_3651_; 
v_toCold_3650_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3651_ = lean_ctor_get(v_toCold_3650_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3651_) == 1)
{
lean_object* v_val_3652_; uint8_t v___x_3653_; 
v_val_3652_ = lean_ctor_get(v_cancelTk_x3f_3651_, 0);
v___x_3653_ = l_IO_CancelToken_isSet(v_val_3652_);
if (v___x_3653_ == 0)
{
goto v___jp_3608_;
}
else
{
lean_object* v___x_3654_; lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_a_3604_);
lean_dec_ref_known(v_e_3272_, 3);
v___x_3654_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
goto v___jp_3608_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref_known(v_e_3272_, 3);
v_a_3710_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3603_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3603_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
goto v___jp_3278_;
}
}
}
case 9:
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_a_3718_ = lean_ctor_get(v_e_3272_, 0);
lean_inc_ref(v_a_3718_);
lean_dec_ref_known(v_e_3272_, 1);
v___x_3719_ = l_Lean_Literal_type(v_a_3718_);
lean_dec_ref(v_a_3718_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
case 10:
{
lean_object* v_expr_3721_; 
v_expr_3721_ = lean_ctor_get(v_e_3272_, 1);
lean_inc_ref(v_expr_3721_);
lean_dec_ref_known(v_e_3272_, 2);
v_e_3272_ = v_expr_3721_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3723_; lean_object* v_idx_3724_; lean_object* v_struct_3725_; uint8_t v_cacheInferType_3742_; 
v_typeName_3723_ = lean_ctor_get(v_e_3272_, 0);
lean_inc(v_typeName_3723_);
v_idx_3724_ = lean_ctor_get(v_e_3272_, 1);
lean_inc(v_idx_3724_);
v_struct_3725_ = lean_ctor_get(v_e_3272_, 2);
lean_inc_ref(v_struct_3725_);
v_cacheInferType_3742_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3742_ == 0)
{
lean_dec_ref_known(v_e_3272_, 3);
goto v___jp_3726_;
}
else
{
uint8_t v___x_3743_; 
v___x_3743_ = l_Lean_Expr_hasMVar(v_e_3272_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3850_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3850_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3850_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3804_; lean_object* v_cache_3805_; lean_object* v_inferType_3806_; lean_object* v___x_3807_; 
v___x_3804_ = lean_st_ref_get(v_a_3274_);
v_cache_3805_ = lean_ctor_get(v___x_3804_, 1);
lean_inc_ref(v_cache_3805_);
lean_dec(v___x_3804_);
v_inferType_3806_ = lean_ctor_get(v_cache_3805_, 0);
lean_inc_ref(v_inferType_3806_);
lean_dec_ref(v_cache_3805_);
v___x_3807_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3806_, v_a_3745_);
if (lean_obj_tag(v___x_3807_) == 1)
{
lean_object* v_val_3808_; lean_object* v_fst_3809_; lean_object* v_snd_3810_; lean_object* v_expr_3811_; uint64_t v_configKey_3812_; lean_object* v_expr_3813_; uint64_t v_configKey_3814_; uint8_t v___x_3815_; 
v_val_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v_fst_3809_ = lean_ctor_get(v_val_3808_, 0);
lean_inc(v_fst_3809_);
v_snd_3810_ = lean_ctor_get(v_val_3808_, 1);
lean_inc(v_snd_3810_);
lean_dec(v_val_3808_);
v_expr_3811_ = lean_ctor_get(v_a_3745_, 0);
v_configKey_3812_ = lean_ctor_get_uint64(v_a_3745_, sizeof(void*)*1);
v_expr_3813_ = lean_ctor_get(v_fst_3809_, 0);
lean_inc_ref(v_expr_3813_);
v_configKey_3814_ = lean_ctor_get_uint64(v_fst_3809_, sizeof(void*)*1);
lean_dec(v_fst_3809_);
v___x_3815_ = lean_uint64_dec_eq(v_configKey_3812_, v_configKey_3814_);
if (v___x_3815_ == 0)
{
lean_dec_ref(v_expr_3813_);
lean_dec(v_snd_3810_);
lean_dec_ref(v_inferType_3806_);
lean_del_object(v___x_3747_);
goto v___jp_3790_;
}
else
{
size_t v___x_3816_; uint8_t v___x_3817_; 
v___x_3816_ = ((size_t)64ULL);
v___x_3817_ = lean_expr_equal_budgeted(v_expr_3811_, v_expr_3813_, v___x_3816_);
lean_dec_ref(v_expr_3813_);
switch(v___x_3817_)
{
case 0:
{
lean_dec(v_snd_3810_);
lean_dec_ref(v_inferType_3806_);
lean_del_object(v___x_3747_);
goto v___jp_3790_;
}
case 1:
{
lean_object* v___x_3819_; 
lean_dec_ref(v_inferType_3806_);
lean_dec(v_a_3745_);
lean_dec_ref(v_struct_3725_);
lean_dec(v_idx_3724_);
lean_dec(v_typeName_3723_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v_snd_3810_);
v___x_3819_ = v___x_3747_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_snd_3810_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
default: 
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_cache_3823_; lean_object* v_mctx_3824_; lean_object* v_zetaDeltaFVarIds_3825_; lean_object* v_postponed_3826_; lean_object* v_diag_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v_snd_3810_);
lean_del_object(v___x_3747_);
v___x_3821_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3806_, v_a_3745_);
v___x_3822_ = lean_st_ref_take(v_a_3274_);
v_cache_3823_ = lean_ctor_get(v___x_3822_, 1);
v_mctx_3824_ = lean_ctor_get(v___x_3822_, 0);
v_zetaDeltaFVarIds_3825_ = lean_ctor_get(v___x_3822_, 2);
v_postponed_3826_ = lean_ctor_get(v___x_3822_, 3);
v_diag_3827_ = lean_ctor_get(v___x_3822_, 4);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3829_ = v___x_3822_;
v_isShared_3830_ = v_isSharedCheck_3849_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_diag_3827_);
lean_inc(v_postponed_3826_);
lean_inc(v_zetaDeltaFVarIds_3825_);
lean_inc(v_cache_3823_);
lean_inc(v_mctx_3824_);
lean_dec(v___x_3822_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3849_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_funInfo_3831_; lean_object* v_synthInstance_3832_; lean_object* v_whnf_3833_; lean_object* v_defEqTrans_3834_; lean_object* v_defEqPerm_3835_; lean_object* v_unfold_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3847_; 
v_funInfo_3831_ = lean_ctor_get(v_cache_3823_, 1);
v_synthInstance_3832_ = lean_ctor_get(v_cache_3823_, 2);
v_whnf_3833_ = lean_ctor_get(v_cache_3823_, 3);
v_defEqTrans_3834_ = lean_ctor_get(v_cache_3823_, 4);
v_defEqPerm_3835_ = lean_ctor_get(v_cache_3823_, 5);
v_unfold_3836_ = lean_ctor_get(v_cache_3823_, 6);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_cache_3823_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v_cache_3823_, 0);
lean_dec(v_unused_3848_);
v___x_3838_ = v_cache_3823_;
v_isShared_3839_ = v_isSharedCheck_3847_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_unfold_3836_);
lean_inc(v_defEqPerm_3835_);
lean_inc(v_defEqTrans_3834_);
lean_inc(v_whnf_3833_);
lean_inc(v_synthInstance_3832_);
lean_inc(v_funInfo_3831_);
lean_dec(v_cache_3823_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3847_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3821_);
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_funInfo_3831_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_synthInstance_3832_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v_whnf_3833_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_defEqTrans_3834_);
lean_ctor_set(v_reuseFailAlloc_3846_, 5, v_defEqPerm_3835_);
lean_ctor_set(v_reuseFailAlloc_3846_, 6, v_unfold_3836_);
v___x_3841_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3843_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v___x_3841_);
v___x_3843_ = v___x_3829_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_mctx_3824_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_zetaDeltaFVarIds_3825_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_postponed_3826_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_diag_3827_);
v___x_3843_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_st_ref_put(v_a_3274_, v___x_3843_);
goto v___jp_3790_;
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
lean_dec(v___x_3807_);
lean_dec_ref(v_inferType_3806_);
lean_del_object(v___x_3747_);
goto v___jp_3790_;
}
v___jp_3749_:
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3723_, v_idx_3724_, v_struct_3725_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; uint8_t v___x_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v___x_3752_ = l_Lean_Expr_hasMVar(v_a_3751_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3788_; 
lean_inc(v_a_3751_);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; 
v_unused_3789_ = lean_ctor_get(v___x_3750_, 0);
lean_dec(v_unused_3789_);
v___x_3754_ = v___x_3750_;
v_isShared_3755_ = v_isSharedCheck_3788_;
goto v_resetjp_3753_;
}
else
{
lean_dec(v___x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3788_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v_cache_3757_; lean_object* v_mctx_3758_; lean_object* v_zetaDeltaFVarIds_3759_; lean_object* v_postponed_3760_; lean_object* v_diag_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3787_; 
v___x_3756_ = lean_st_ref_take(v_a_3274_);
v_cache_3757_ = lean_ctor_get(v___x_3756_, 1);
v_mctx_3758_ = lean_ctor_get(v___x_3756_, 0);
v_zetaDeltaFVarIds_3759_ = lean_ctor_get(v___x_3756_, 2);
v_postponed_3760_ = lean_ctor_get(v___x_3756_, 3);
v_diag_3761_ = lean_ctor_get(v___x_3756_, 4);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3763_ = v___x_3756_;
v_isShared_3764_ = v_isSharedCheck_3787_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_diag_3761_);
lean_inc(v_postponed_3760_);
lean_inc(v_zetaDeltaFVarIds_3759_);
lean_inc(v_cache_3757_);
lean_inc(v_mctx_3758_);
lean_dec(v___x_3756_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3787_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_inferType_3765_; lean_object* v_funInfo_3766_; lean_object* v_synthInstance_3767_; lean_object* v_whnf_3768_; lean_object* v_defEqTrans_3769_; lean_object* v_defEqPerm_3770_; lean_object* v_unfold_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3786_; 
v_inferType_3765_ = lean_ctor_get(v_cache_3757_, 0);
v_funInfo_3766_ = lean_ctor_get(v_cache_3757_, 1);
v_synthInstance_3767_ = lean_ctor_get(v_cache_3757_, 2);
v_whnf_3768_ = lean_ctor_get(v_cache_3757_, 3);
v_defEqTrans_3769_ = lean_ctor_get(v_cache_3757_, 4);
v_defEqPerm_3770_ = lean_ctor_get(v_cache_3757_, 5);
v_unfold_3771_ = lean_ctor_get(v_cache_3757_, 6);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_cache_3757_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3773_ = v_cache_3757_;
v_isShared_3774_ = v_isSharedCheck_3786_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_unfold_3771_);
lean_inc(v_defEqPerm_3770_);
lean_inc(v_defEqTrans_3769_);
lean_inc(v_whnf_3768_);
lean_inc(v_synthInstance_3767_);
lean_inc(v_funInfo_3766_);
lean_inc(v_inferType_3765_);
lean_dec(v_cache_3757_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3786_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3777_; 
lean_inc(v_a_3751_);
v___x_3775_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3765_, v_a_3745_, v_a_3751_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3775_);
v___x_3777_ = v___x_3773_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_funInfo_3766_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_synthInstance_3767_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_whnf_3768_);
lean_ctor_set(v_reuseFailAlloc_3785_, 4, v_defEqTrans_3769_);
lean_ctor_set(v_reuseFailAlloc_3785_, 5, v_defEqPerm_3770_);
lean_ctor_set(v_reuseFailAlloc_3785_, 6, v_unfold_3771_);
v___x_3777_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3777_);
v___x_3779_ = v___x_3763_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_mctx_3758_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3784_, 2, v_zetaDeltaFVarIds_3759_);
lean_ctor_set(v_reuseFailAlloc_3784_, 3, v_postponed_3760_);
lean_ctor_set(v_reuseFailAlloc_3784_, 4, v_diag_3761_);
v___x_3779_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_st_ref_put(v_a_3274_, v___x_3779_);
if (v_isShared_3755_ == 0)
{
v___x_3782_ = v___x_3754_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3751_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3745_);
return v___x_3750_;
}
}
else
{
lean_dec(v_a_3745_);
return v___x_3750_;
}
}
v___jp_3790_:
{
lean_object* v_toCold_3791_; lean_object* v_cancelTk_x3f_3792_; 
v_toCold_3791_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3792_ = lean_ctor_get(v_toCold_3791_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3792_) == 1)
{
lean_object* v_val_3793_; uint8_t v___x_3794_; 
v_val_3793_ = lean_ctor_get(v_cancelTk_x3f_3792_, 0);
v___x_3794_ = l_IO_CancelToken_isSet(v_val_3793_);
if (v___x_3794_ == 0)
{
goto v___jp_3749_;
}
else
{
lean_object* v___x_3795_; lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec(v_a_3745_);
lean_dec_ref(v_struct_3725_);
lean_dec(v_idx_3724_);
lean_dec(v_typeName_3723_);
v___x_3795_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
goto v___jp_3749_;
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v_struct_3725_);
lean_dec(v_idx_3724_);
lean_dec(v_typeName_3723_);
v_a_3851_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3744_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3744_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3272_, 3);
goto v___jp_3726_;
}
}
v___jp_3726_:
{
lean_object* v_toCold_3727_; lean_object* v_cancelTk_x3f_3728_; 
v_toCold_3727_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3728_ = lean_ctor_get(v_toCold_3727_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3728_) == 1)
{
lean_object* v_val_3729_; uint8_t v___x_3730_; 
v_val_3729_ = lean_ctor_get(v_cancelTk_x3f_3728_, 0);
v___x_3730_ = l_IO_CancelToken_isSet(v_val_3729_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3723_, v_idx_3724_, v_struct_3725_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3731_;
}
else
{
lean_object* v___x_3732_; lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_struct_3725_);
lean_dec(v_idx_3724_);
lean_dec(v_typeName_3723_);
v___x_3732_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v___x_3741_; 
v___x_3741_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3723_, v_idx_3724_, v_struct_3725_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3741_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3859_; 
v_cacheInferType_3859_ = lean_ctor_get_uint8(v_a_3273_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3859_ == 0)
{
goto v___jp_3294_;
}
else
{
uint8_t v___x_3860_; 
v___x_3860_ = l_Lean_Expr_hasMVar(v_e_3272_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_inc_ref(v_e_3272_);
v___x_3861_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3272_, v_a_3273_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3967_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3967_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3967_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3921_; lean_object* v_cache_3922_; lean_object* v_inferType_3923_; lean_object* v___x_3924_; 
v___x_3921_ = lean_st_ref_get(v_a_3274_);
v_cache_3922_ = lean_ctor_get(v___x_3921_, 1);
lean_inc_ref(v_cache_3922_);
lean_dec(v___x_3921_);
v_inferType_3923_ = lean_ctor_get(v_cache_3922_, 0);
lean_inc_ref(v_inferType_3923_);
lean_dec_ref(v_cache_3922_);
v___x_3924_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3923_, v_a_3862_);
if (lean_obj_tag(v___x_3924_) == 1)
{
lean_object* v_val_3925_; lean_object* v_fst_3926_; lean_object* v_snd_3927_; lean_object* v_expr_3928_; uint64_t v_configKey_3929_; lean_object* v_expr_3930_; uint64_t v_configKey_3931_; uint8_t v___x_3932_; 
v_val_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_val_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v_fst_3926_ = lean_ctor_get(v_val_3925_, 0);
lean_inc(v_fst_3926_);
v_snd_3927_ = lean_ctor_get(v_val_3925_, 1);
lean_inc(v_snd_3927_);
lean_dec(v_val_3925_);
v_expr_3928_ = lean_ctor_get(v_a_3862_, 0);
v_configKey_3929_ = lean_ctor_get_uint64(v_a_3862_, sizeof(void*)*1);
v_expr_3930_ = lean_ctor_get(v_fst_3926_, 0);
lean_inc_ref(v_expr_3930_);
v_configKey_3931_ = lean_ctor_get_uint64(v_fst_3926_, sizeof(void*)*1);
lean_dec(v_fst_3926_);
v___x_3932_ = lean_uint64_dec_eq(v_configKey_3929_, v_configKey_3931_);
if (v___x_3932_ == 0)
{
lean_dec_ref(v_expr_3930_);
lean_dec(v_snd_3927_);
lean_dec_ref(v_inferType_3923_);
lean_del_object(v___x_3864_);
goto v___jp_3907_;
}
else
{
size_t v___x_3933_; uint8_t v___x_3934_; 
v___x_3933_ = ((size_t)64ULL);
v___x_3934_ = lean_expr_equal_budgeted(v_expr_3928_, v_expr_3930_, v___x_3933_);
lean_dec_ref(v_expr_3930_);
switch(v___x_3934_)
{
case 0:
{
lean_dec(v_snd_3927_);
lean_dec_ref(v_inferType_3923_);
lean_del_object(v___x_3864_);
goto v___jp_3907_;
}
case 1:
{
lean_object* v___x_3936_; 
lean_dec_ref(v_inferType_3923_);
lean_dec(v_a_3862_);
lean_dec_ref(v_e_3272_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_snd_3927_);
v___x_3936_ = v___x_3864_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_snd_3927_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
default: 
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v_cache_3940_; lean_object* v_mctx_3941_; lean_object* v_zetaDeltaFVarIds_3942_; lean_object* v_postponed_3943_; lean_object* v_diag_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_snd_3927_);
lean_del_object(v___x_3864_);
v___x_3938_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3923_, v_a_3862_);
v___x_3939_ = lean_st_ref_take(v_a_3274_);
v_cache_3940_ = lean_ctor_get(v___x_3939_, 1);
v_mctx_3941_ = lean_ctor_get(v___x_3939_, 0);
v_zetaDeltaFVarIds_3942_ = lean_ctor_get(v___x_3939_, 2);
v_postponed_3943_ = lean_ctor_get(v___x_3939_, 3);
v_diag_3944_ = lean_ctor_get(v___x_3939_, 4);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3946_ = v___x_3939_;
v_isShared_3947_ = v_isSharedCheck_3966_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_diag_3944_);
lean_inc(v_postponed_3943_);
lean_inc(v_zetaDeltaFVarIds_3942_);
lean_inc(v_cache_3940_);
lean_inc(v_mctx_3941_);
lean_dec(v___x_3939_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3966_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v_funInfo_3948_; lean_object* v_synthInstance_3949_; lean_object* v_whnf_3950_; lean_object* v_defEqTrans_3951_; lean_object* v_defEqPerm_3952_; lean_object* v_unfold_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3964_; 
v_funInfo_3948_ = lean_ctor_get(v_cache_3940_, 1);
v_synthInstance_3949_ = lean_ctor_get(v_cache_3940_, 2);
v_whnf_3950_ = lean_ctor_get(v_cache_3940_, 3);
v_defEqTrans_3951_ = lean_ctor_get(v_cache_3940_, 4);
v_defEqPerm_3952_ = lean_ctor_get(v_cache_3940_, 5);
v_unfold_3953_ = lean_ctor_get(v_cache_3940_, 6);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_cache_3940_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v_cache_3940_, 0);
lean_dec(v_unused_3965_);
v___x_3955_ = v_cache_3940_;
v_isShared_3956_ = v_isSharedCheck_3964_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_unfold_3953_);
lean_inc(v_defEqPerm_3952_);
lean_inc(v_defEqTrans_3951_);
lean_inc(v_whnf_3950_);
lean_inc(v_synthInstance_3949_);
lean_inc(v_funInfo_3948_);
lean_dec(v_cache_3940_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3964_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3938_);
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_funInfo_3948_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_synthInstance_3949_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v_whnf_3950_);
lean_ctor_set(v_reuseFailAlloc_3963_, 4, v_defEqTrans_3951_);
lean_ctor_set(v_reuseFailAlloc_3963_, 5, v_defEqPerm_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 6, v_unfold_3953_);
v___x_3958_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; 
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 1, v___x_3958_);
v___x_3960_ = v___x_3946_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_mctx_3941_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_zetaDeltaFVarIds_3942_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_postponed_3943_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_diag_3944_);
v___x_3960_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_st_ref_put(v_a_3274_, v___x_3960_);
goto v___jp_3907_;
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
lean_dec(v___x_3924_);
lean_dec_ref(v_inferType_3923_);
lean_del_object(v___x_3864_);
goto v___jp_3907_;
}
v___jp_3866_:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; uint8_t v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v___x_3869_ = l_Lean_Expr_hasMVar(v_a_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3905_; 
lean_inc(v_a_3868_);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3905_ == 0)
{
lean_object* v_unused_3906_; 
v_unused_3906_ = lean_ctor_get(v___x_3867_, 0);
lean_dec(v_unused_3906_);
v___x_3871_ = v___x_3867_;
v_isShared_3872_ = v_isSharedCheck_3905_;
goto v_resetjp_3870_;
}
else
{
lean_dec(v___x_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3905_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v_cache_3874_; lean_object* v_mctx_3875_; lean_object* v_zetaDeltaFVarIds_3876_; lean_object* v_postponed_3877_; lean_object* v_diag_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3904_; 
v___x_3873_ = lean_st_ref_take(v_a_3274_);
v_cache_3874_ = lean_ctor_get(v___x_3873_, 1);
v_mctx_3875_ = lean_ctor_get(v___x_3873_, 0);
v_zetaDeltaFVarIds_3876_ = lean_ctor_get(v___x_3873_, 2);
v_postponed_3877_ = lean_ctor_get(v___x_3873_, 3);
v_diag_3878_ = lean_ctor_get(v___x_3873_, 4);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3880_ = v___x_3873_;
v_isShared_3881_ = v_isSharedCheck_3904_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_diag_3878_);
lean_inc(v_postponed_3877_);
lean_inc(v_zetaDeltaFVarIds_3876_);
lean_inc(v_cache_3874_);
lean_inc(v_mctx_3875_);
lean_dec(v___x_3873_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3904_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_inferType_3882_; lean_object* v_funInfo_3883_; lean_object* v_synthInstance_3884_; lean_object* v_whnf_3885_; lean_object* v_defEqTrans_3886_; lean_object* v_defEqPerm_3887_; lean_object* v_unfold_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3903_; 
v_inferType_3882_ = lean_ctor_get(v_cache_3874_, 0);
v_funInfo_3883_ = lean_ctor_get(v_cache_3874_, 1);
v_synthInstance_3884_ = lean_ctor_get(v_cache_3874_, 2);
v_whnf_3885_ = lean_ctor_get(v_cache_3874_, 3);
v_defEqTrans_3886_ = lean_ctor_get(v_cache_3874_, 4);
v_defEqPerm_3887_ = lean_ctor_get(v_cache_3874_, 5);
v_unfold_3888_ = lean_ctor_get(v_cache_3874_, 6);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_cache_3874_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3890_ = v_cache_3874_;
v_isShared_3891_ = v_isSharedCheck_3903_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_unfold_3888_);
lean_inc(v_defEqPerm_3887_);
lean_inc(v_defEqTrans_3886_);
lean_inc(v_whnf_3885_);
lean_inc(v_synthInstance_3884_);
lean_inc(v_funInfo_3883_);
lean_inc(v_inferType_3882_);
lean_dec(v_cache_3874_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3903_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3892_; lean_object* v___x_3894_; 
lean_inc(v_a_3868_);
v___x_3892_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3882_, v_a_3862_, v_a_3868_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3892_);
v___x_3894_ = v___x_3890_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_funInfo_3883_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_synthInstance_3884_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_whnf_3885_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_defEqTrans_3886_);
lean_ctor_set(v_reuseFailAlloc_3902_, 5, v_defEqPerm_3887_);
lean_ctor_set(v_reuseFailAlloc_3902_, 6, v_unfold_3888_);
v___x_3894_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v___x_3894_);
v___x_3896_ = v___x_3880_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_mctx_3875_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_zetaDeltaFVarIds_3876_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v_postponed_3877_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_diag_3878_);
v___x_3896_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3897_; lean_object* v___x_3899_; 
v___x_3897_ = lean_st_ref_put(v_a_3274_, v___x_3896_);
if (v_isShared_3872_ == 0)
{
v___x_3899_ = v___x_3871_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3868_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3862_);
return v___x_3867_;
}
}
else
{
lean_dec(v_a_3862_);
return v___x_3867_;
}
}
v___jp_3907_:
{
lean_object* v_toCold_3908_; lean_object* v_cancelTk_x3f_3909_; 
v_toCold_3908_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3909_ = lean_ctor_get(v_toCold_3908_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3909_) == 1)
{
lean_object* v_val_3910_; uint8_t v___x_3911_; 
v_val_3910_ = lean_ctor_get(v_cancelTk_x3f_3909_, 0);
v___x_3911_ = l_IO_CancelToken_isSet(v_val_3910_);
if (v___x_3911_ == 0)
{
goto v___jp_3866_;
}
else
{
lean_object* v___x_3912_; lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_a_3862_);
lean_dec_ref(v_e_3272_);
v___x_3912_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
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
else
{
goto v___jp_3866_;
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v_e_3272_);
v_a_3968_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3861_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3861_);
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
else
{
goto v___jp_3294_;
}
}
}
}
v___jp_3278_:
{
lean_object* v_toCold_3279_; lean_object* v_cancelTk_x3f_3280_; 
v_toCold_3279_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3280_ = lean_ctor_get(v_toCold_3279_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3280_) == 1)
{
lean_object* v_val_3281_; uint8_t v___x_3282_; 
v_val_3281_ = lean_ctor_get(v_cancelTk_x3f_3280_, 0);
v___x_3282_ = l_IO_CancelToken_isSet(v_val_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v_e_3272_);
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
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3293_;
}
}
v___jp_3294_:
{
lean_object* v_toCold_3295_; lean_object* v_cancelTk_x3f_3296_; 
v_toCold_3295_ = lean_ctor_get(v_a_3275_, 0);
v_cancelTk_x3f_3296_ = lean_ctor_get(v_toCold_3295_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3296_) == 1)
{
lean_object* v_val_3297_; uint8_t v___x_3298_; 
v_val_3297_ = lean_ctor_get(v_cancelTk_x3f_3296_, 0);
v___x_3298_ = l_IO_CancelToken_isSet(v_val_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_e_3272_);
v___x_3300_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
return v___x_3309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3983_, lean_object* v_x_3984_, lean_object* v_x_3985_, lean_object* v_x_3986_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3984_, v_x_3985_, v_x_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3989_, v_x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3992_, v_x_3993_, v_x_3994_);
lean_dec_ref(v_x_3994_);
lean_dec_ref(v_x_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(lean_object* v_00_u03b2_3996_, lean_object* v_x_3997_, lean_object* v_x_3998_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3997_, v_x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___boxed(lean_object* v_00_u03b2_4000_, lean_object* v_x_4001_, lean_object* v_x_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(v_00_u03b2_4000_, v_x_4001_, v_x_4002_);
lean_dec_ref(v_x_4002_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_4004_, lean_object* v_x_4005_, size_t v_x_4006_, size_t v_x_4007_, lean_object* v_x_4008_, lean_object* v_x_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_4005_, v_x_4006_, v_x_4007_, v_x_4008_, v_x_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4011_, lean_object* v_x_4012_, lean_object* v_x_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_){
_start:
{
size_t v_x_5606__boxed_4017_; size_t v_x_5607__boxed_4018_; lean_object* v_res_4019_; 
v_x_5606__boxed_4017_ = lean_unbox_usize(v_x_4013_);
lean_dec(v_x_4013_);
v_x_5607__boxed_4018_ = lean_unbox_usize(v_x_4014_);
lean_dec(v_x_4014_);
v_res_4019_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_4011_, v_x_4012_, v_x_5606__boxed_4017_, v_x_5607__boxed_4018_, v_x_4015_, v_x_4016_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_4020_, lean_object* v_x_4021_, size_t v_x_4022_, lean_object* v_x_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_4021_, v_x_4022_, v_x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v_x_4028_){
_start:
{
size_t v_x_5623__boxed_4029_; lean_object* v_res_4030_; 
v_x_5623__boxed_4029_ = lean_unbox_usize(v_x_4027_);
lean_dec(v_x_4027_);
v_res_4030_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_4025_, v_x_4026_, v_x_5623__boxed_4029_, v_x_4028_);
lean_dec_ref(v_x_4028_);
lean_dec_ref(v_x_4026_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(lean_object* v_00_u03b2_4031_, lean_object* v_x_4032_, size_t v_x_4033_, lean_object* v_x_4034_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_4032_, v_x_4033_, v_x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4036_, lean_object* v_x_4037_, lean_object* v_x_4038_, lean_object* v_x_4039_){
_start:
{
size_t v_x_5634__boxed_4040_; lean_object* v_res_4041_; 
v_x_5634__boxed_4040_ = lean_unbox_usize(v_x_4038_);
lean_dec(v_x_4038_);
v_res_4041_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(v_00_u03b2_4036_, v_x_4037_, v_x_5634__boxed_4040_, v_x_4039_);
lean_dec_ref(v_x_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4042_, lean_object* v_n_4043_, lean_object* v_k_4044_, lean_object* v_v_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_4043_, v_k_4044_, v_v_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_4047_, size_t v_depth_4048_, lean_object* v_keys_4049_, lean_object* v_vals_4050_, lean_object* v_heq_4051_, lean_object* v_i_4052_, lean_object* v_entries_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_4048_, v_keys_4049_, v_vals_4050_, v_i_4052_, v_entries_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_depth_4056_, lean_object* v_keys_4057_, lean_object* v_vals_4058_, lean_object* v_heq_4059_, lean_object* v_i_4060_, lean_object* v_entries_4061_){
_start:
{
size_t v_depth_boxed_4062_; lean_object* v_res_4063_; 
v_depth_boxed_4062_ = lean_unbox_usize(v_depth_4056_);
lean_dec(v_depth_4056_);
v_res_4063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_4055_, v_depth_boxed_4062_, v_keys_4057_, v_vals_4058_, v_heq_4059_, v_i_4060_, v_entries_4061_);
lean_dec_ref(v_vals_4058_);
lean_dec_ref(v_keys_4057_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4064_, lean_object* v_keys_4065_, lean_object* v_vals_4066_, lean_object* v_heq_4067_, lean_object* v_i_4068_, lean_object* v_k_4069_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_4065_, v_vals_4066_, v_i_4068_, v_k_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4071_, lean_object* v_keys_4072_, lean_object* v_vals_4073_, lean_object* v_heq_4074_, lean_object* v_i_4075_, lean_object* v_k_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_4071_, v_keys_4072_, v_vals_4073_, v_heq_4074_, v_i_4075_, v_k_4076_);
lean_dec_ref(v_k_4076_);
lean_dec_ref(v_vals_4073_);
lean_dec_ref(v_keys_4072_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_x_4079_, v_x_4080_, v_x_4081_, v_x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = l_Lean_maxRecDepthErrorMessage;
v___x_4090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_4092_ = l_Lean_MessageData_ofFormat(v___x_4091_);
return v___x_4092_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_4094_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_4095_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___x_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_4096_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v_ref_4096_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_4104_, lean_object* v_ref_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4105_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_4112_, lean_object* v_ref_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_4112_, v_ref_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4173_; uint8_t v_beta_4174_; 
v___x_4173_ = l_Lean_Meta_Context_config(v___y_4121_);
v_beta_4174_ = lean_ctor_get_uint8(v___x_4173_, 13);
if (v_beta_4174_ == 0)
{
lean_dec_ref(v___x_4173_);
goto v___jp_4126_;
}
else
{
uint8_t v_iota_4175_; 
v_iota_4175_ = lean_ctor_get_uint8(v___x_4173_, 12);
if (v_iota_4175_ == 0)
{
lean_dec_ref(v___x_4173_);
goto v___jp_4126_;
}
else
{
uint8_t v_zeta_4176_; 
v_zeta_4176_ = lean_ctor_get_uint8(v___x_4173_, 15);
if (v_zeta_4176_ == 0)
{
lean_dec_ref(v___x_4173_);
goto v___jp_4126_;
}
else
{
uint8_t v_zetaHave_4177_; 
v_zetaHave_4177_ = lean_ctor_get_uint8(v___x_4173_, 18);
if (v_zetaHave_4177_ == 0)
{
lean_dec_ref(v___x_4173_);
goto v___jp_4126_;
}
else
{
uint8_t v_zetaDelta_4178_; 
v_zetaDelta_4178_ = lean_ctor_get_uint8(v___x_4173_, 16);
if (v_zetaDelta_4178_ == 0)
{
lean_dec_ref(v___x_4173_);
goto v___jp_4126_;
}
else
{
uint8_t v_etaStruct_4179_; uint8_t v_proj_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v_etaStruct_4179_ = lean_ctor_get_uint8(v___x_4173_, 10);
v_proj_4180_ = lean_ctor_get_uint8(v___x_4173_, 14);
lean_dec_ref(v___x_4173_);
v___x_4181_ = lean_box(v_proj_4180_);
v___x_4182_ = lean_obj_tag_nat(v___x_4181_);
lean_dec(v___x_4181_);
v___x_4183_ = lean_unsigned_to_nat(2u);
v___x_4184_ = lean_nat_dec_eq(v___x_4182_, v___x_4183_);
if (v___x_4184_ == 0)
{
goto v___jp_4126_;
}
else
{
uint8_t v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = 0;
v___x_4186_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4179_, v___x_4185_);
if (v___x_4186_ == 0)
{
goto v___jp_4126_;
}
else
{
lean_object* v___x_4187_; 
v___x_4187_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec_ref(v___y_4121_);
return v___x_4187_;
}
}
}
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4127_; uint8_t v_foApprox_4128_; uint8_t v_ctxApprox_4129_; uint8_t v_quasiPatternApprox_4130_; uint8_t v_constApprox_4131_; uint8_t v_isDefEqStuckEx_4132_; uint8_t v_unificationHints_4133_; uint8_t v_proofIrrelevance_4134_; uint8_t v_assignSyntheticOpaque_4135_; uint8_t v_offsetCnstrs_4136_; uint8_t v_transparency_4137_; uint8_t v_univApprox_4138_; uint8_t v_zetaUnused_4139_; uint8_t v_canUnfoldPredicateConfig_4140_; uint8_t v_stringLitToCtor_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4172_; 
v___x_4127_ = l_Lean_Meta_Context_config(v___y_4121_);
v_foApprox_4128_ = lean_ctor_get_uint8(v___x_4127_, 0);
v_ctxApprox_4129_ = lean_ctor_get_uint8(v___x_4127_, 1);
v_quasiPatternApprox_4130_ = lean_ctor_get_uint8(v___x_4127_, 2);
v_constApprox_4131_ = lean_ctor_get_uint8(v___x_4127_, 3);
v_isDefEqStuckEx_4132_ = lean_ctor_get_uint8(v___x_4127_, 4);
v_unificationHints_4133_ = lean_ctor_get_uint8(v___x_4127_, 5);
v_proofIrrelevance_4134_ = lean_ctor_get_uint8(v___x_4127_, 6);
v_assignSyntheticOpaque_4135_ = lean_ctor_get_uint8(v___x_4127_, 7);
v_offsetCnstrs_4136_ = lean_ctor_get_uint8(v___x_4127_, 8);
v_transparency_4137_ = lean_ctor_get_uint8(v___x_4127_, 9);
v_univApprox_4138_ = lean_ctor_get_uint8(v___x_4127_, 11);
v_zetaUnused_4139_ = lean_ctor_get_uint8(v___x_4127_, 17);
v_canUnfoldPredicateConfig_4140_ = lean_ctor_get_uint8(v___x_4127_, 19);
v_stringLitToCtor_4141_ = lean_ctor_get_uint8(v___x_4127_, 20);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4143_ = v___x_4127_;
v_isShared_4144_ = v_isSharedCheck_4172_;
goto v_resetjp_4142_;
}
else
{
lean_dec(v___x_4127_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4172_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
uint8_t v___x_4145_; uint8_t v___x_4146_; uint8_t v___x_4147_; lean_object* v___x_4149_; 
v___x_4145_ = 1;
v___x_4146_ = 0;
v___x_4147_ = 2;
if (v_isShared_4144_ == 0)
{
v___x_4149_ = v___x_4143_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 0, v_foApprox_4128_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 1, v_ctxApprox_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 2, v_quasiPatternApprox_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 3, v_constApprox_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 4, v_isDefEqStuckEx_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 5, v_unificationHints_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 6, v_proofIrrelevance_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 7, v_assignSyntheticOpaque_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 8, v_offsetCnstrs_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 9, v_transparency_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 11, v_univApprox_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 17, v_zetaUnused_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 19, v_canUnfoldPredicateConfig_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4171_, 20, v_stringLitToCtor_4141_);
v___x_4149_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
uint8_t v_trackZetaDelta_4150_; lean_object* v_zetaDeltaSet_4151_; lean_object* v_lctx_4152_; lean_object* v_localInstances_4153_; lean_object* v_defEqCtx_x3f_4154_; lean_object* v_synthPendingDepth_4155_; lean_object* v_customCanUnfoldPredicate_x3f_4156_; uint8_t v_univApprox_4157_; uint8_t v_inTypeClassResolution_4158_; uint8_t v_cacheInferType_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4169_; 
lean_ctor_set_uint8(v___x_4149_, 10, v___x_4146_);
lean_ctor_set_uint8(v___x_4149_, 12, v___x_4145_);
lean_ctor_set_uint8(v___x_4149_, 13, v___x_4145_);
lean_ctor_set_uint8(v___x_4149_, 14, v___x_4147_);
lean_ctor_set_uint8(v___x_4149_, 15, v___x_4145_);
lean_ctor_set_uint8(v___x_4149_, 16, v___x_4145_);
lean_ctor_set_uint8(v___x_4149_, 18, v___x_4145_);
v_trackZetaDelta_4150_ = lean_ctor_get_uint8(v___y_4121_, sizeof(void*)*7);
v_zetaDeltaSet_4151_ = lean_ctor_get(v___y_4121_, 1);
v_lctx_4152_ = lean_ctor_get(v___y_4121_, 2);
v_localInstances_4153_ = lean_ctor_get(v___y_4121_, 3);
v_defEqCtx_x3f_4154_ = lean_ctor_get(v___y_4121_, 4);
v_synthPendingDepth_4155_ = lean_ctor_get(v___y_4121_, 5);
v_customCanUnfoldPredicate_x3f_4156_ = lean_ctor_get(v___y_4121_, 6);
v_univApprox_4157_ = lean_ctor_get_uint8(v___y_4121_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4158_ = lean_ctor_get_uint8(v___y_4121_, sizeof(void*)*7 + 2);
v_cacheInferType_4159_ = lean_ctor_get_uint8(v___y_4121_, sizeof(void*)*7 + 3);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___y_4121_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v___y_4121_, 0);
lean_dec(v_unused_4170_);
v___x_4161_ = v___y_4121_;
v_isShared_4162_ = v_isSharedCheck_4169_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4156_);
lean_inc(v_synthPendingDepth_4155_);
lean_inc(v_defEqCtx_x3f_4154_);
lean_inc(v_localInstances_4153_);
lean_inc(v_lctx_4152_);
lean_inc(v_zetaDeltaSet_4151_);
lean_dec(v___y_4121_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4169_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
uint64_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4149_);
v___x_4164_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4164_, 0, v___x_4149_);
lean_ctor_set_uint64(v___x_4164_, sizeof(void*)*1, v___x_4163_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4164_);
v___x_4166_ = v___x_4161_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v_zetaDeltaSet_4151_);
lean_ctor_set(v_reuseFailAlloc_4168_, 2, v_lctx_4152_);
lean_ctor_set(v_reuseFailAlloc_4168_, 3, v_localInstances_4153_);
lean_ctor_set(v_reuseFailAlloc_4168_, 4, v_defEqCtx_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4168_, 5, v_synthPendingDepth_4155_);
lean_ctor_set(v_reuseFailAlloc_4168_, 6, v_customCanUnfoldPredicate_x3f_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*7, v_trackZetaDelta_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*7 + 1, v_univApprox_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*7 + 3, v_cacheInferType_4159_);
v___x_4166_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4120_, v___x_4166_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec_ref(v___x_4166_);
return v___x_4167_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
lean_object* v___y_4202_; lean_object* v_toCold_4219_; lean_object* v_currRecDepth_4220_; lean_object* v_ref_4221_; uint16_t v_optionFlags_4222_; uint8_t v_suppressElabErrors_4223_; uint8_t v_checkDeprecated_4224_; uint8_t v_isRecordingDeps_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4265_; 
v_toCold_4219_ = lean_ctor_get(v_a_4198_, 0);
v_currRecDepth_4220_ = lean_ctor_get(v_a_4198_, 1);
v_ref_4221_ = lean_ctor_get(v_a_4198_, 2);
v_optionFlags_4222_ = lean_ctor_get_uint16(v_a_4198_, sizeof(void*)*3);
v_suppressElabErrors_4223_ = lean_ctor_get_uint8(v_a_4198_, sizeof(void*)*3 + 2);
v_checkDeprecated_4224_ = lean_ctor_get_uint8(v_a_4198_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4225_ = lean_ctor_get_uint8(v_a_4198_, sizeof(void*)*3 + 4);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_a_4198_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4227_ = v_a_4198_;
v_isShared_4228_ = v_isSharedCheck_4265_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_ref_4221_);
lean_inc(v_currRecDepth_4220_);
lean_inc(v_toCold_4219_);
lean_dec(v_a_4198_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4265_;
goto v_resetjp_4226_;
}
v___jp_4201_:
{
if (lean_obj_tag(v___y_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_a_4203_ = lean_ctor_get(v___y_4202_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___y_4202_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___y_4202_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___y_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___y_4202_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___y_4202_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___y_4202_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___y_4202_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
v_resetjp_4226_:
{
lean_object* v_maxRecDepth_4229_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_maxRecDepth_4229_ = lean_ctor_get(v_toCold_4219_, 3);
v___x_4261_ = lean_unsigned_to_nat(0u);
v___x_4262_ = lean_nat_dec_eq(v_maxRecDepth_4229_, v___x_4261_);
if (v___x_4262_ == 0)
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_nat_dec_eq(v_currRecDepth_4220_, v_maxRecDepth_4229_);
if (v___x_4263_ == 0)
{
goto v___jp_4230_;
}
else
{
lean_object* v___x_4264_; 
lean_del_object(v___x_4227_);
lean_dec(v_currRecDepth_4220_);
lean_dec_ref(v_toCold_4219_);
lean_dec(v_a_4199_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec_ref(v_e_4195_);
v___x_4264_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4221_);
return v___x_4264_;
}
}
else
{
goto v___jp_4230_;
}
v___jp_4230_:
{
lean_object* v___x_4231_; uint8_t v_transparency_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4231_ = l_Lean_Meta_Context_config(v_a_4196_);
v_transparency_4232_ = lean_ctor_get_uint8(v___x_4231_, 9);
lean_dec_ref(v___x_4231_);
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_nat_add(v_currRecDepth_4220_, v___x_4233_);
lean_dec(v_currRecDepth_4220_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 1, v___x_4234_);
v___x_4236_ = v___x_4227_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_toCold_4219_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4260_, 2, v_ref_4221_);
lean_ctor_set_uint16(v_reuseFailAlloc_4260_, sizeof(void*)*3, v_optionFlags_4222_);
lean_ctor_set_uint8(v_reuseFailAlloc_4260_, sizeof(void*)*3 + 2, v_suppressElabErrors_4223_);
lean_ctor_set_uint8(v_reuseFailAlloc_4260_, sizeof(void*)*3 + 3, v_checkDeprecated_4224_);
lean_ctor_set_uint8(v_reuseFailAlloc_4260_, sizeof(void*)*3 + 4, v_isRecordingDeps_4225_);
v___x_4236_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
uint8_t v___x_4237_; uint8_t v___x_4238_; 
v___x_4237_ = 1;
v___x_4238_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4232_, v___x_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4195_, v_a_4196_, v_a_4197_, v___x_4236_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v___x_4236_);
lean_dec(v_a_4197_);
v___y_4202_ = v___x_4239_;
goto v___jp_4201_;
}
else
{
lean_object* v_keyedConfig_4240_; uint8_t v_trackZetaDelta_4241_; lean_object* v_zetaDeltaSet_4242_; lean_object* v_lctx_4243_; lean_object* v_localInstances_4244_; lean_object* v_defEqCtx_x3f_4245_; lean_object* v_synthPendingDepth_4246_; lean_object* v_customCanUnfoldPredicate_x3f_4247_; uint8_t v_univApprox_4248_; uint8_t v_inTypeClassResolution_4249_; uint8_t v_cacheInferType_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4259_; 
v_keyedConfig_4240_ = lean_ctor_get(v_a_4196_, 0);
v_trackZetaDelta_4241_ = lean_ctor_get_uint8(v_a_4196_, sizeof(void*)*7);
v_zetaDeltaSet_4242_ = lean_ctor_get(v_a_4196_, 1);
v_lctx_4243_ = lean_ctor_get(v_a_4196_, 2);
v_localInstances_4244_ = lean_ctor_get(v_a_4196_, 3);
v_defEqCtx_x3f_4245_ = lean_ctor_get(v_a_4196_, 4);
v_synthPendingDepth_4246_ = lean_ctor_get(v_a_4196_, 5);
v_customCanUnfoldPredicate_x3f_4247_ = lean_ctor_get(v_a_4196_, 6);
v_univApprox_4248_ = lean_ctor_get_uint8(v_a_4196_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4249_ = lean_ctor_get_uint8(v_a_4196_, sizeof(void*)*7 + 2);
v_cacheInferType_4250_ = lean_ctor_get_uint8(v_a_4196_, sizeof(void*)*7 + 3);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_a_4196_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4252_ = v_a_4196_;
v_isShared_4253_ = v_isSharedCheck_4259_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4247_);
lean_inc(v_synthPendingDepth_4246_);
lean_inc(v_defEqCtx_x3f_4245_);
lean_inc(v_localInstances_4244_);
lean_inc(v_lctx_4243_);
lean_inc(v_zetaDeltaSet_4242_);
lean_inc(v_keyedConfig_4240_);
lean_dec(v_a_4196_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4259_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4254_; lean_object* v___x_4256_; 
v___x_4254_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4237_, v_keyedConfig_4240_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4254_);
v___x_4256_ = v___x_4252_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4254_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_zetaDeltaSet_4242_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_lctx_4243_);
lean_ctor_set(v_reuseFailAlloc_4258_, 3, v_localInstances_4244_);
lean_ctor_set(v_reuseFailAlloc_4258_, 4, v_defEqCtx_x3f_4245_);
lean_ctor_set(v_reuseFailAlloc_4258_, 5, v_synthPendingDepth_4246_);
lean_ctor_set(v_reuseFailAlloc_4258_, 6, v_customCanUnfoldPredicate_x3f_4247_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*7, v_trackZetaDelta_4241_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*7 + 1, v_univApprox_4248_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4258_, sizeof(void*)*7 + 3, v_cacheInferType_4250_);
v___x_4256_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4195_, v___x_4256_, v_a_4197_, v___x_4236_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v___x_4236_);
lean_dec(v_a_4197_);
v___y_4202_ = v___x_4257_;
goto v___jp_4201_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = lean_infer_type(v_e_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_4273_){
_start:
{
switch(lean_obj_tag(v_x_4273_))
{
case 0:
{
uint8_t v___x_4274_; 
v___x_4274_ = 1;
return v___x_4274_;
}
case 2:
{
lean_object* v_a_4275_; lean_object* v_a_4276_; uint8_t v___x_4277_; 
v_a_4275_ = lean_ctor_get(v_x_4273_, 0);
v_a_4276_ = lean_ctor_get(v_x_4273_, 1);
v___x_4277_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4275_);
if (v___x_4277_ == 0)
{
return v___x_4277_;
}
else
{
v_x_4273_ = v_a_4276_;
goto _start;
}
}
case 3:
{
lean_object* v_a_4279_; 
v_a_4279_ = lean_ctor_get(v_x_4273_, 1);
v_x_4273_ = v_a_4279_;
goto _start;
}
default: 
{
uint8_t v___x_4281_; 
v___x_4281_ = 0;
return v___x_4281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_4282_);
lean_dec(v_x_4282_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; lean_object* v_mctx_4289_; lean_object* v___x_4290_; lean_object* v_fst_4291_; lean_object* v_snd_4292_; lean_object* v___x_4293_; lean_object* v_cache_4294_; lean_object* v_zetaDeltaFVarIds_4295_; lean_object* v_postponed_4296_; lean_object* v_diag_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4306_; 
v___x_4288_ = lean_st_ref_get(v___y_4286_);
v_mctx_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc_ref(v_mctx_4289_);
lean_dec(v___x_4288_);
v___x_4290_ = lean_instantiate_level_mvars(v_mctx_4289_, v_l_4285_);
v_fst_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_fst_4291_);
v_snd_4292_ = lean_ctor_get(v___x_4290_, 1);
lean_inc(v_snd_4292_);
lean_dec_ref(v___x_4290_);
v___x_4293_ = lean_st_ref_take(v___y_4286_);
v_cache_4294_ = lean_ctor_get(v___x_4293_, 1);
v_zetaDeltaFVarIds_4295_ = lean_ctor_get(v___x_4293_, 2);
v_postponed_4296_ = lean_ctor_get(v___x_4293_, 3);
v_diag_4297_ = lean_ctor_get(v___x_4293_, 4);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v___x_4293_, 0);
lean_dec(v_unused_4307_);
v___x_4299_ = v___x_4293_;
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_diag_4297_);
lean_inc(v_postponed_4296_);
lean_inc(v_zetaDeltaFVarIds_4295_);
lean_inc(v_cache_4294_);
lean_dec(v___x_4293_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v_fst_4291_);
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_fst_4291_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v_cache_4294_);
lean_ctor_set(v_reuseFailAlloc_4305_, 2, v_zetaDeltaFVarIds_4295_);
lean_ctor_set(v_reuseFailAlloc_4305_, 3, v_postponed_4296_);
lean_ctor_set(v_reuseFailAlloc_4305_, 4, v_diag_4297_);
v___x_4302_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = lean_st_ref_put(v___y_4286_, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_snd_4292_);
return v___x_4304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4308_, v___y_4309_);
lean_dec(v___y_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4312_, v___y_4314_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_00_u03c3_4326_, lean_object* v_x_4327_, lean_object* v_x_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v___y_4339_; 
switch(lean_obj_tag(v_x_4327_))
{
case 3:
{
lean_object* v_u_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v_u_4360_ = lean_ctor_get(v_x_4327_, 0);
lean_inc(v_u_4360_);
lean_dec_ref_known(v_x_4327_, 1);
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = lean_nat_dec_eq(v_x_4328_, v___x_4361_);
lean_dec(v_x_4328_);
if (v___x_4362_ == 0)
{
lean_dec(v_u_4360_);
lean_dec_ref(v_00_u03c3_4326_);
goto v___jp_4334_;
}
else
{
lean_object* v_paramNames_4363_; lean_object* v_lvls_4364_; uint8_t v___x_4365_; 
v_paramNames_4363_ = lean_ctor_get(v_00_u03c3_4326_, 0);
lean_inc(v_paramNames_4363_);
v_lvls_4364_ = lean_ctor_get(v_00_u03c3_4326_, 1);
lean_inc(v_lvls_4364_);
lean_dec_ref(v_00_u03c3_4326_);
v___x_4365_ = l_List_isEmpty___redArg(v_paramNames_4363_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Lean_Level_instantiateParams(v_u_4360_, v_paramNames_4363_, v_lvls_4364_);
v___y_4339_ = v___x_4366_;
goto v___jp_4338_;
}
else
{
lean_dec(v_lvls_4364_);
lean_dec(v_paramNames_4363_);
v___y_4339_ = v_u_4360_;
goto v___jp_4338_;
}
}
}
case 7:
{
lean_object* v_body_4367_; lean_object* v_zero_4368_; uint8_t v_isZero_4369_; 
v_body_4367_ = lean_ctor_get(v_x_4327_, 2);
lean_inc_ref(v_body_4367_);
lean_dec_ref_known(v_x_4327_, 3);
v_zero_4368_ = lean_unsigned_to_nat(0u);
v_isZero_4369_ = lean_nat_dec_eq(v_x_4328_, v_zero_4368_);
if (v_isZero_4369_ == 1)
{
uint8_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_dec_ref(v_body_4367_);
lean_dec(v_x_4328_);
lean_dec_ref(v_00_u03c3_4326_);
v___x_4370_ = 0;
v___x_4371_ = lean_box(v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4371_);
return v___x_4372_;
}
else
{
lean_object* v_one_4373_; lean_object* v_n_4374_; 
v_one_4373_ = lean_unsigned_to_nat(1u);
v_n_4374_ = lean_nat_sub(v_x_4328_, v_one_4373_);
lean_dec(v_x_4328_);
v_x_4327_ = v_body_4367_;
v_x_4328_ = v_n_4374_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4376_; 
v_body_4376_ = lean_ctor_get(v_x_4327_, 3);
lean_inc_ref(v_body_4376_);
lean_dec_ref_known(v_x_4327_, 4);
v_x_4327_ = v_body_4376_;
goto _start;
}
case 10:
{
lean_object* v_expr_4378_; 
v_expr_4378_ = lean_ctor_get(v_x_4327_, 1);
lean_inc_ref(v_expr_4378_);
lean_dec_ref_known(v_x_4327_, 2);
v_x_4327_ = v_expr_4378_;
goto _start;
}
default: 
{
lean_dec(v_x_4328_);
lean_dec_ref(v_x_4327_);
lean_dec_ref(v_00_u03c3_4326_);
goto v___jp_4334_;
}
}
v___jp_4334_:
{
uint8_t v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = 2;
v___x_4336_ = lean_box(v___x_4335_);
v___x_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
return v___x_4337_;
}
v___jp_4338_:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v___y_4339_, v_a_4330_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4351_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4343_ = v___x_4340_;
v_isShared_4344_ = v_isSharedCheck_4351_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4351_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
uint8_t v___x_4345_; uint8_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4345_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4341_);
lean_dec(v_a_4341_);
v___x_4346_ = l_Lean_Bool_toLBool(v___x_4345_);
v___x_4347_ = lean_box(v___x_4346_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v___x_4347_);
v___x_4349_ = v___x_4343_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
v_a_4352_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4340_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4340_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_00_u03c3_4380_, lean_object* v_x_4381_, lean_object* v_x_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_00_u03c3_4380_, v_x_4381_, v_x_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object* v_00_u03c3_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
if (lean_obj_tag(v_a_4390_) == 0)
{
lean_object* v___x_4392_; 
lean_dec_ref(v_00_u03c3_4389_);
v___x_4392_ = l_List_reverse___redArg(v_a_4391_);
return v___x_4392_;
}
else
{
lean_object* v_head_4393_; lean_object* v_tail_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4408_; 
v_head_4393_ = lean_ctor_get(v_a_4390_, 0);
v_tail_4394_ = lean_ctor_get(v_a_4390_, 1);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_a_4390_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4396_ = v_a_4390_;
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_tail_4394_);
lean_inc(v_head_4393_);
lean_dec(v_a_4390_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___y_4399_; lean_object* v_paramNames_4404_; lean_object* v_lvls_4405_; uint8_t v___x_4406_; 
v_paramNames_4404_ = lean_ctor_get(v_00_u03c3_4389_, 0);
v_lvls_4405_ = lean_ctor_get(v_00_u03c3_4389_, 1);
v___x_4406_ = l_List_isEmpty___redArg(v_paramNames_4404_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; 
lean_inc(v_lvls_4405_);
lean_inc(v_paramNames_4404_);
v___x_4407_ = l_Lean_Level_instantiateParams(v_head_4393_, v_paramNames_4404_, v_lvls_4405_);
v___y_4399_ = v___x_4407_;
goto v___jp_4398_;
}
else
{
v___y_4399_ = v_head_4393_;
goto v___jp_4398_;
}
v___jp_4398_:
{
lean_object* v___x_4401_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 1, v_a_4391_);
lean_ctor_set(v___x_4396_, 0, v___y_4399_);
v___x_4401_ = v___x_4396_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___y_4399_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_a_4391_);
v___x_4401_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
v_a_4390_ = v_tail_4394_;
v_a_4391_ = v___x_4401_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_00_u03c3_4411_, lean_object* v_x_4412_, lean_object* v_x_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
switch(lean_obj_tag(v_x_4412_))
{
case 4:
{
lean_object* v_declName_4419_; lean_object* v_us_4420_; lean_object* v___y_4422_; lean_object* v_paramNames_4436_; uint8_t v___x_4437_; 
v_declName_4419_ = lean_ctor_get(v_x_4412_, 0);
lean_inc(v_declName_4419_);
v_us_4420_ = lean_ctor_get(v_x_4412_, 1);
lean_inc(v_us_4420_);
lean_dec_ref_known(v_x_4412_, 2);
v_paramNames_4436_ = lean_ctor_get(v_00_u03c3_4411_, 0);
v___x_4437_ = l_List_isEmpty___redArg(v_paramNames_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = lean_box(0);
v___x_4439_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4411_, v_us_4420_, v___x_4438_);
v___y_4422_ = v___x_4439_;
goto v___jp_4421_;
}
else
{
lean_dec_ref(v_00_u03c3_4411_);
v___y_4422_ = v_us_4420_;
goto v___jp_4421_;
}
v___jp_4421_:
{
lean_object* v___x_4423_; 
v___x_4423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4419_, v___y_4422_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v_fst_4425_; lean_object* v_snd_4426_; lean_object* v___x_4427_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v_fst_4425_ = lean_ctor_get(v_a_4424_, 0);
lean_inc(v_fst_4425_);
v_snd_4426_ = lean_ctor_get(v_a_4424_, 1);
lean_inc(v_snd_4426_);
lean_dec(v_a_4424_);
v___x_4427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4426_, v_fst_4425_, v_x_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4427_;
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec(v_x_4413_);
v_a_4428_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4423_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4423_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_4440_; lean_object* v___x_4441_; 
lean_dec_ref(v_00_u03c3_4411_);
v_fvarId_4440_ = lean_ctor_get(v_x_4412_, 0);
lean_inc(v_fvarId_4440_);
lean_dec_ref_known(v_x_4412_, 1);
v___x_4441_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4440_, v_a_4414_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4441_, 1);
v___x_4443_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4444_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4443_, v_a_4442_, v_x_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4444_;
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_x_4413_);
v_a_4445_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4441_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4441_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4453_; lean_object* v___x_4454_; 
lean_dec_ref(v_00_u03c3_4411_);
v_mvarId_4453_ = lean_ctor_get(v_x_4412_, 0);
lean_inc(v_mvarId_4453_);
lean_dec_ref_known(v_x_4412_, 1);
v___x_4454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4453_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v___x_4456_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4457_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4456_, v_a_4455_, v_x_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4457_;
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec(v_x_4413_);
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
case 5:
{
lean_object* v_fn_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v_fn_4466_ = lean_ctor_get(v_x_4412_, 0);
lean_inc_ref(v_fn_4466_);
lean_dec_ref_known(v_x_4412_, 2);
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_add(v_x_4413_, v___x_4467_);
lean_dec(v_x_4413_);
v_x_4412_ = v_fn_4466_;
v_x_4413_ = v___x_4468_;
goto _start;
}
case 10:
{
lean_object* v_expr_4470_; 
v_expr_4470_ = lean_ctor_get(v_x_4412_, 1);
lean_inc_ref(v_expr_4470_);
lean_dec_ref_known(v_x_4412_, 2);
v_x_4412_ = v_expr_4470_;
goto _start;
}
case 8:
{
lean_object* v_body_4472_; 
v_body_4472_ = lean_ctor_get(v_x_4412_, 3);
lean_inc_ref(v_body_4472_);
lean_dec_ref_known(v_x_4412_, 4);
v_x_4412_ = v_body_4472_;
goto _start;
}
case 6:
{
lean_object* v_body_4474_; lean_object* v_zero_4475_; uint8_t v_isZero_4476_; 
v_body_4474_ = lean_ctor_get(v_x_4412_, 2);
lean_inc_ref(v_body_4474_);
lean_dec_ref_known(v_x_4412_, 3);
v_zero_4475_ = lean_unsigned_to_nat(0u);
v_isZero_4476_ = lean_nat_dec_eq(v_x_4413_, v_zero_4475_);
if (v_isZero_4476_ == 1)
{
uint8_t v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_dec_ref(v_body_4474_);
lean_dec(v_x_4413_);
lean_dec_ref(v_00_u03c3_4411_);
v___x_4477_ = 0;
v___x_4478_ = lean_box(v___x_4477_);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
else
{
lean_object* v_one_4480_; lean_object* v_n_4481_; 
v_one_4480_ = lean_unsigned_to_nat(1u);
v_n_4481_ = lean_nat_sub(v_x_4413_, v_one_4480_);
lean_dec(v_x_4413_);
v_x_4412_ = v_body_4474_;
v_x_4413_ = v_n_4481_;
goto _start;
}
}
default: 
{
uint8_t v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
lean_dec(v_x_4413_);
lean_dec_ref(v_x_4412_);
lean_dec_ref(v_00_u03c3_4411_);
v___x_4483_ = 2;
v___x_4484_ = lean_box(v___x_4483_);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
return v___x_4485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_00_u03c3_4486_, lean_object* v_x_4487_, lean_object* v_x_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4486_, v_x_4487_, v_x_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object* v_00_u03c3_4495_, lean_object* v_x_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
switch(lean_obj_tag(v_x_4496_))
{
case 1:
{
lean_object* v_fvarId_4502_; lean_object* v___x_4503_; 
lean_dec_ref(v_00_u03c3_4495_);
v_fvarId_4502_ = lean_ctor_get(v_x_4496_, 0);
lean_inc(v_fvarId_4502_);
lean_dec_ref_known(v_x_4496_, 1);
v___x_4503_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4502_, v_a_4497_, v_a_4499_, v_a_4500_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___x_4505_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4506_ = lean_unsigned_to_nat(0u);
v___x_4507_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4505_, v_a_4504_, v___x_4506_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4507_;
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_a_4508_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4503_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4503_);
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
case 2:
{
lean_object* v_mvarId_4516_; lean_object* v___x_4517_; 
lean_dec_ref(v_00_u03c3_4495_);
v_mvarId_4516_ = lean_ctor_get(v_x_4496_, 0);
lean_inc(v_mvarId_4516_);
lean_dec_ref_known(v_x_4496_, 1);
v___x_4517_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4516_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4519_, v_a_4518_, v___x_4520_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4521_;
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_a_4522_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4517_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4517_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
case 3:
{
uint8_t v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_dec_ref_known(v_x_4496_, 1);
lean_dec_ref(v_00_u03c3_4495_);
v___x_4530_ = 0;
v___x_4531_ = lean_box(v___x_4530_);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
return v___x_4532_;
}
case 4:
{
lean_object* v_declName_4533_; lean_object* v_us_4534_; lean_object* v___y_4536_; lean_object* v_paramNames_4551_; uint8_t v___x_4552_; 
v_declName_4533_ = lean_ctor_get(v_x_4496_, 0);
lean_inc(v_declName_4533_);
v_us_4534_ = lean_ctor_get(v_x_4496_, 1);
lean_inc(v_us_4534_);
lean_dec_ref_known(v_x_4496_, 2);
v_paramNames_4551_ = lean_ctor_get(v_00_u03c3_4495_, 0);
v___x_4552_ = l_List_isEmpty___redArg(v_paramNames_4551_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = lean_box(0);
v___x_4554_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4495_, v_us_4534_, v___x_4553_);
v___y_4536_ = v___x_4554_;
goto v___jp_4535_;
}
else
{
lean_dec_ref(v_00_u03c3_4495_);
v___y_4536_ = v_us_4534_;
goto v___jp_4535_;
}
v___jp_4535_:
{
lean_object* v___x_4537_; 
v___x_4537_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4533_, v___y_4536_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v_fst_4539_; lean_object* v_snd_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v_fst_4539_ = lean_ctor_get(v_a_4538_, 0);
lean_inc(v_fst_4539_);
v_snd_4540_ = lean_ctor_get(v_a_4538_, 1);
lean_inc(v_snd_4540_);
lean_dec(v_a_4538_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4540_, v_fst_4539_, v___x_4541_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4542_;
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_a_4543_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4537_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4537_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v_fn_4555_ = lean_ctor_get(v_x_4496_, 0);
lean_inc_ref(v_fn_4555_);
lean_dec_ref_known(v_x_4496_, 2);
v___x_4556_ = lean_unsigned_to_nat(1u);
v___x_4557_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4495_, v_fn_4555_, v___x_4556_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4557_;
}
case 6:
{
uint8_t v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec_ref_known(v_x_4496_, 3);
lean_dec_ref(v_00_u03c3_4495_);
v___x_4558_ = 0;
v___x_4559_ = lean_box(v___x_4558_);
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
case 7:
{
lean_object* v_body_4561_; 
v_body_4561_ = lean_ctor_get(v_x_4496_, 2);
lean_inc_ref(v_body_4561_);
lean_dec_ref_known(v_x_4496_, 3);
v_x_4496_ = v_body_4561_;
goto _start;
}
case 8:
{
lean_object* v_body_4563_; 
v_body_4563_ = lean_ctor_get(v_x_4496_, 3);
lean_inc_ref(v_body_4563_);
lean_dec_ref_known(v_x_4496_, 4);
v_x_4496_ = v_body_4563_;
goto _start;
}
case 9:
{
uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
lean_dec_ref_known(v_x_4496_, 1);
lean_dec_ref(v_00_u03c3_4495_);
v___x_4565_ = 0;
v___x_4566_ = lean_box(v___x_4565_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
return v___x_4567_;
}
case 10:
{
lean_object* v_expr_4568_; 
v_expr_4568_ = lean_ctor_get(v_x_4496_, 1);
lean_inc_ref(v_expr_4568_);
lean_dec_ref_known(v_x_4496_, 2);
v_x_4496_ = v_expr_4568_;
goto _start;
}
default: 
{
uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
lean_dec_ref(v_x_4496_);
lean_dec_ref(v_00_u03c3_4495_);
v___x_4570_ = 2;
v___x_4571_ = lean_box(v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object* v_00_u03c3_4573_, lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4573_, v_x_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_e_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4588_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v___x_4587_, v_e_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_e_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_Meta_isPropQuick(v_e_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v___x_4602_; 
lean_inc_ref(v_e_4596_);
v___x_4602_ = l_Lean_Meta_isPropQuick(v_e_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4659_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4659_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4659_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
uint8_t v___x_4607_; 
v___x_4607_ = lean_unbox(v_a_4603_);
lean_dec(v_a_4603_);
switch(v___x_4607_)
{
case 0:
{
uint8_t v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_dec_ref(v_e_4596_);
v___x_4608_ = 0;
v___x_4609_ = lean_box(v___x_4608_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4609_);
v___x_4611_ = v___x_4605_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
case 1:
{
uint8_t v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4616_; 
lean_dec_ref(v_e_4596_);
v___x_4613_ = 1;
v___x_4614_ = lean_box(v___x_4613_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4614_);
v___x_4616_ = v___x_4605_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
default: 
{
lean_object* v___x_4618_; 
lean_del_object(v___x_4605_);
lean_inc(v_a_4600_);
lean_inc_ref(v_a_4599_);
lean_inc(v_a_4598_);
lean_inc_ref(v_a_4597_);
v___x_4618_ = lean_infer_type(v_e_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4620_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_a_4619_);
lean_dec_ref_known(v___x_4618_, 1);
v___x_4620_ = l_Lean_Meta_whnfD(v_a_4619_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4642_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4642_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4642_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
if (lean_obj_tag(v_a_4621_) == 3)
{
lean_object* v_u_4625_; lean_object* v___x_4626_; lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4636_; 
lean_del_object(v___x_4623_);
v_u_4625_ = lean_ctor_get(v_a_4621_, 0);
lean_inc(v_u_4625_);
lean_dec_ref_known(v_a_4621_, 1);
v___x_4626_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4625_, v_a_4598_);
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4636_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
uint8_t v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4631_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4627_);
lean_dec(v_a_4627_);
v___x_4632_ = lean_box(v___x_4631_);
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4632_);
v___x_4634_ = v___x_4629_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
else
{
uint8_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4640_; 
lean_dec(v_a_4621_);
v___x_4637_ = 0;
v___x_4638_ = lean_box(v___x_4637_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v___x_4638_);
v___x_4640_ = v___x_4623_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
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
else
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4620_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4620_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
v_a_4651_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4618_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4618_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec_ref(v_e_4596_);
v_a_4660_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4602_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4602_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Lean_Meta_isProp(v_e_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4675_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_obj_tag_nat(v_x_4675_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4677_);
lean_dec(v_x_4677_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4679_, lean_object* v_k_4680_){
_start:
{
if (lean_obj_tag(v_t_4679_) == 3)
{
lean_object* v_idx_4681_; lean_object* v_numArgs_4682_; lean_object* v___x_4683_; 
v_idx_4681_ = lean_ctor_get(v_t_4679_, 0);
lean_inc(v_idx_4681_);
v_numArgs_4682_ = lean_ctor_get(v_t_4679_, 1);
lean_inc(v_numArgs_4682_);
lean_dec_ref_known(v_t_4679_, 2);
v___x_4683_ = lean_apply_2(v_k_4680_, v_idx_4681_, v_numArgs_4682_);
return v___x_4683_;
}
else
{
lean_dec(v_t_4679_);
return v_k_4680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4684_, lean_object* v_ctorIdx_4685_, lean_object* v_t_4686_, lean_object* v_h_4687_, lean_object* v_k_4688_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4686_, v_k_4688_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4690_, lean_object* v_ctorIdx_4691_, lean_object* v_t_4692_, lean_object* v_h_4693_, lean_object* v_k_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4690_, v_ctorIdx_4691_, v_t_4692_, v_h_4693_, v_k_4694_);
lean_dec(v_ctorIdx_4691_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4696_, lean_object* v_false_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4696_, v_false_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4699_, lean_object* v_t_4700_, lean_object* v_h_4701_, lean_object* v_false_4702_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4700_, v_false_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4704_, lean_object* v_true_4705_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4704_, v_true_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4707_, lean_object* v_t_4708_, lean_object* v_h_4709_, lean_object* v_true_4710_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4708_, v_true_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4712_, lean_object* v_undef_4713_){
_start:
{
lean_object* v___x_4714_; 
v___x_4714_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4712_, v_undef_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4715_, lean_object* v_t_4716_, lean_object* v_h_4717_, lean_object* v_undef_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4716_, v_undef_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4720_, lean_object* v_bvar_4721_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4720_, v_bvar_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4723_, lean_object* v_t_4724_, lean_object* v_h_4725_, lean_object* v_bvar_4726_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4724_, v_bvar_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4728_){
_start:
{
switch(v_x_4728_)
{
case 0:
{
lean_object* v___x_4729_; 
v___x_4729_ = lean_box(0);
return v___x_4729_;
}
case 1:
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_box(1);
return v___x_4730_;
}
default: 
{
lean_object* v___x_4731_; 
v___x_4731_ = lean_box(2);
return v___x_4731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4732_){
_start:
{
uint8_t v_x_25__boxed_4733_; lean_object* v_res_4734_; 
v_x_25__boxed_4733_ = lean_unbox(v_x_4732_);
v_res_4734_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4733_);
return v_res_4734_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4735_){
_start:
{
switch(lean_obj_tag(v_x_4735_))
{
case 0:
{
uint8_t v___x_4736_; 
v___x_4736_ = 0;
return v___x_4736_;
}
case 1:
{
uint8_t v___x_4737_; 
v___x_4737_ = 1;
return v___x_4737_;
}
default: 
{
uint8_t v___x_4738_; 
v___x_4738_ = 2;
return v___x_4738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4739_){
_start:
{
uint8_t v_res_4740_; lean_object* v_r_4741_; 
v_res_4740_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4739_);
lean_dec(v_x_4739_);
v_r_4741_ = lean_box(v_res_4740_);
return v_r_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_00_u03c3_4743_, lean_object* v_e_4744_, lean_object* v_numArgs_4745_){
_start:
{
lean_object* v___y_4747_; 
switch(lean_obj_tag(v_e_4744_))
{
case 3:
{
lean_object* v_u_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; 
v_u_4753_ = lean_ctor_get(v_e_4744_, 0);
lean_inc(v_u_4753_);
lean_dec_ref_known(v_e_4744_, 1);
v___x_4754_ = lean_unsigned_to_nat(0u);
v___x_4755_ = lean_nat_dec_eq(v_numArgs_4745_, v___x_4754_);
lean_dec(v_numArgs_4745_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; 
lean_dec(v_u_4753_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4756_ = lean_box(2);
return v___x_4756_;
}
else
{
lean_object* v_paramNames_4757_; lean_object* v_lvls_4758_; uint8_t v___x_4759_; 
v_paramNames_4757_ = lean_ctor_get(v_00_u03c3_4743_, 0);
lean_inc(v_paramNames_4757_);
v_lvls_4758_ = lean_ctor_get(v_00_u03c3_4743_, 1);
lean_inc(v_lvls_4758_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4759_ = l_List_isEmpty___redArg(v_paramNames_4757_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Lean_Level_instantiateParams(v_u_4753_, v_paramNames_4757_, v_lvls_4758_);
v___y_4747_ = v___x_4760_;
goto v___jp_4746_;
}
else
{
lean_dec(v_lvls_4758_);
lean_dec(v_paramNames_4757_);
v___y_4747_ = v_u_4753_;
goto v___jp_4746_;
}
}
}
case 7:
{
lean_object* v_body_4761_; lean_object* v_zero_4762_; uint8_t v_isZero_4763_; 
v_body_4761_ = lean_ctor_get(v_e_4744_, 2);
lean_inc_ref(v_body_4761_);
lean_dec_ref_known(v_e_4744_, 3);
v_zero_4762_ = lean_unsigned_to_nat(0u);
v_isZero_4763_ = lean_nat_dec_eq(v_numArgs_4745_, v_zero_4762_);
if (v_isZero_4763_ == 0)
{
lean_object* v_one_4764_; lean_object* v_n_4765_; 
v_one_4764_ = lean_unsigned_to_nat(1u);
v_n_4765_ = lean_nat_sub(v_numArgs_4745_, v_one_4764_);
lean_dec(v_numArgs_4745_);
v_e_4744_ = v_body_4761_;
v_numArgs_4745_ = v_n_4765_;
goto _start;
}
else
{
lean_object* v___x_4767_; 
lean_dec_ref(v_body_4761_);
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4767_ = lean_box(2);
return v___x_4767_;
}
}
case 10:
{
lean_object* v_expr_4768_; 
v_expr_4768_ = lean_ctor_get(v_e_4744_, 1);
lean_inc_ref(v_expr_4768_);
lean_dec_ref_known(v_e_4744_, 2);
v_e_4744_ = v_expr_4768_;
goto _start;
}
case 5:
{
lean_object* v_fn_4770_; 
v_fn_4770_ = lean_ctor_get(v_e_4744_, 0);
if (lean_obj_tag(v_fn_4770_) == 4)
{
lean_object* v_declName_4771_; 
v_declName_4771_ = lean_ctor_get(v_fn_4770_, 0);
lean_inc(v_declName_4771_);
if (lean_obj_tag(v_declName_4771_) == 1)
{
lean_object* v_pre_4772_; 
v_pre_4772_ = lean_ctor_get(v_declName_4771_, 0);
if (lean_obj_tag(v_pre_4772_) == 0)
{
lean_object* v_arg_4773_; lean_object* v_str_4774_; lean_object* v___x_4775_; uint8_t v___x_4776_; 
v_arg_4773_ = lean_ctor_get(v_e_4744_, 1);
lean_inc_ref(v_arg_4773_);
lean_dec_ref_known(v_e_4744_, 2);
v_str_4774_ = lean_ctor_get(v_declName_4771_, 1);
lean_inc_ref(v_str_4774_);
lean_dec_ref_known(v_declName_4771_, 2);
v___x_4775_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4776_ = lean_string_dec_eq(v_str_4774_, v___x_4775_);
lean_dec_ref(v_str_4774_);
if (v___x_4776_ == 0)
{
lean_object* v___x_4777_; 
lean_dec_ref(v_arg_4773_);
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4777_ = lean_box(2);
return v___x_4777_;
}
else
{
v_e_4744_ = v_arg_4773_;
goto _start;
}
}
else
{
lean_object* v___x_4779_; 
lean_dec_ref_known(v_declName_4771_, 2);
lean_dec_ref_known(v_e_4744_, 2);
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4779_ = lean_box(2);
return v___x_4779_;
}
}
else
{
lean_object* v___x_4780_; 
lean_dec(v_declName_4771_);
lean_dec_ref_known(v_e_4744_, 2);
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4780_ = lean_box(2);
return v___x_4780_;
}
}
else
{
lean_object* v___x_4781_; 
lean_dec_ref_known(v_e_4744_, 2);
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4781_ = lean_box(2);
return v___x_4781_;
}
}
default: 
{
lean_object* v___x_4782_; 
lean_dec(v_numArgs_4745_);
lean_dec_ref(v_e_4744_);
lean_dec_ref(v_00_u03c3_4743_);
v___x_4782_ = lean_box(2);
return v___x_4782_;
}
}
v___jp_4746_:
{
uint8_t v___x_4748_; 
v___x_4748_ = l_Lean_Level_isNeverZero(v___y_4747_);
if (v___x_4748_ == 0)
{
uint8_t v___x_4749_; 
v___x_4749_ = l_Lean_Level_isZero(v___y_4747_);
lean_dec(v___y_4747_);
if (v___x_4749_ == 0)
{
lean_object* v___x_4750_; 
v___x_4750_ = lean_box(2);
return v___x_4750_;
}
else
{
lean_object* v___x_4751_; 
v___x_4751_ = lean_box(1);
return v___x_4751_;
}
}
else
{
lean_object* v___x_4752_; 
lean_dec(v___y_4747_);
v___x_4752_ = lean_box(0);
return v___x_4752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_00_u03c3_4783_, lean_object* v_r_4784_, lean_object* v_binderType_4785_){
_start:
{
if (lean_obj_tag(v_r_4784_) == 3)
{
lean_object* v_idx_4786_; lean_object* v_numArgs_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4799_; 
v_idx_4786_ = lean_ctor_get(v_r_4784_, 0);
v_numArgs_4787_ = lean_ctor_get(v_r_4784_, 1);
v_isSharedCheck_4799_ = !lean_is_exclusive(v_r_4784_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4789_ = v_r_4784_;
v_isShared_4790_ = v_isSharedCheck_4799_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_numArgs_4787_);
lean_inc(v_idx_4786_);
lean_dec(v_r_4784_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4799_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v_zero_4791_; uint8_t v_isZero_4792_; 
v_zero_4791_ = lean_unsigned_to_nat(0u);
v_isZero_4792_ = lean_nat_dec_eq(v_idx_4786_, v_zero_4791_);
if (v_isZero_4792_ == 1)
{
lean_object* v___x_4793_; 
lean_del_object(v___x_4789_);
lean_dec(v_idx_4786_);
v___x_4793_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_00_u03c3_4783_, v_binderType_4785_, v_numArgs_4787_);
return v___x_4793_;
}
else
{
lean_object* v_one_4794_; lean_object* v_n_4795_; lean_object* v___x_4797_; 
lean_dec_ref(v_binderType_4785_);
lean_dec_ref(v_00_u03c3_4783_);
v_one_4794_ = lean_unsigned_to_nat(1u);
v_n_4795_ = lean_nat_sub(v_idx_4786_, v_one_4794_);
lean_dec(v_idx_4786_);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v_n_4795_);
v___x_4797_ = v___x_4789_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_n_4795_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_numArgs_4787_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_4785_);
lean_dec_ref(v_00_u03c3_4783_);
return v_r_4784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_00_u03c3_4800_, lean_object* v_x_4801_, lean_object* v_x_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v_type_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; 
switch(lean_obj_tag(v_x_4801_))
{
case 7:
{
lean_object* v_binderType_4841_; lean_object* v_body_4842_; lean_object* v_zero_4843_; uint8_t v_isZero_4844_; 
v_binderType_4841_ = lean_ctor_get(v_x_4801_, 1);
v_body_4842_ = lean_ctor_get(v_x_4801_, 2);
v_zero_4843_ = lean_unsigned_to_nat(0u);
v_isZero_4844_ = lean_nat_dec_eq(v_x_4802_, v_zero_4843_);
if (v_isZero_4844_ == 1)
{
v_type_4809_ = v_x_4801_;
v___y_4810_ = v_a_4803_;
v___y_4811_ = v_a_4804_;
v___y_4812_ = v_a_4805_;
v___y_4813_ = v_a_4806_;
goto v___jp_4808_;
}
else
{
lean_object* v_one_4845_; lean_object* v_n_4846_; lean_object* v___x_4847_; 
lean_inc_ref(v_body_4842_);
lean_inc_ref(v_binderType_4841_);
lean_dec_ref_known(v_x_4801_, 3);
v_one_4845_ = lean_unsigned_to_nat(1u);
v_n_4846_ = lean_nat_sub(v_x_4802_, v_one_4845_);
lean_inc_ref(v_00_u03c3_4800_);
v___x_4847_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4800_, v_body_4842_, v_n_4846_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
lean_dec(v_n_4846_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4856_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4856_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4856_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___x_4852_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4800_, v_a_4848_, v_binderType_4841_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 0, v___x_4852_);
v___x_4854_ = v___x_4850_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
else
{
lean_dec_ref(v_binderType_4841_);
lean_dec_ref(v_00_u03c3_4800_);
return v___x_4847_;
}
}
}
case 8:
{
lean_object* v_type_4857_; lean_object* v_body_4858_; lean_object* v___x_4859_; 
v_type_4857_ = lean_ctor_get(v_x_4801_, 1);
lean_inc_ref(v_type_4857_);
v_body_4858_ = lean_ctor_get(v_x_4801_, 3);
lean_inc_ref(v_body_4858_);
lean_dec_ref_known(v_x_4801_, 4);
lean_inc_ref(v_00_u03c3_4800_);
v___x_4859_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4800_, v_body_4858_, v_x_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4868_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4862_ = v___x_4859_;
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4859_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4864_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4800_, v_a_4860_, v_type_4857_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 0, v___x_4864_);
v___x_4866_ = v___x_4862_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
else
{
lean_dec_ref(v_type_4857_);
lean_dec_ref(v_00_u03c3_4800_);
return v___x_4859_;
}
}
case 10:
{
lean_object* v_expr_4869_; 
v_expr_4869_ = lean_ctor_get(v_x_4801_, 1);
lean_inc_ref(v_expr_4869_);
lean_dec_ref_known(v_x_4801_, 2);
v_x_4801_ = v_expr_4869_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; 
lean_dec_ref(v_00_u03c3_4800_);
v_deBruijnIndex_4871_ = lean_ctor_get(v_x_4801_, 0);
lean_inc(v_deBruijnIndex_4871_);
lean_dec_ref_known(v_x_4801_, 1);
v___x_4872_ = lean_unsigned_to_nat(0u);
v___x_4873_ = lean_nat_dec_eq(v_x_4802_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_dec(v_deBruijnIndex_4871_);
goto v___jp_4838_;
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4874_, 0, v_deBruijnIndex_4871_);
lean_ctor_set(v___x_4874_, 1, v___x_4872_);
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
return v___x_4875_;
}
}
default: 
{
lean_object* v___x_4876_; uint8_t v___x_4877_; 
v___x_4876_ = lean_unsigned_to_nat(0u);
v___x_4877_ = lean_nat_dec_eq(v_x_4802_, v___x_4876_);
if (v___x_4877_ == 0)
{
lean_dec_ref(v_x_4801_);
lean_dec_ref(v_00_u03c3_4800_);
goto v___jp_4838_;
}
else
{
v_type_4809_ = v_x_4801_;
v___y_4810_ = v_a_4803_;
v___y_4811_ = v_a_4804_;
v___y_4812_ = v_a_4805_;
v___y_4813_ = v_a_4806_;
goto v___jp_4808_;
}
}
}
v___jp_4808_:
{
lean_object* v___x_4814_; 
v___x_4814_ = l_Lean_Expr_getAppFn(v_type_4809_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_deBruijnIndex_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_dec_ref(v_00_u03c3_4800_);
v_deBruijnIndex_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_deBruijnIndex_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v___x_4816_ = l_Lean_Expr_getAppNumArgs(v_type_4809_);
lean_dec_ref(v_type_4809_);
v___x_4817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4817_, 0, v_deBruijnIndex_4815_);
lean_ctor_set(v___x_4817_, 1, v___x_4816_);
v___x_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4817_);
return v___x_4818_;
}
else
{
lean_object* v___x_4819_; 
lean_dec_ref(v___x_4814_);
v___x_4819_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4800_, v_type_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4829_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4822_ = v___x_4819_;
v_isShared_4823_ = v_isSharedCheck_4829_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4819_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4829_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
uint8_t v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; 
v___x_4824_ = lean_unbox(v_a_4820_);
lean_dec(v_a_4820_);
v___x_4825_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4824_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4825_);
v___x_4827_ = v___x_4822_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
v_a_4830_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4819_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4819_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
v___jp_4838_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = lean_box(2);
v___x_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_00_u03c3_4878_, lean_object* v_x_4879_, lean_object* v_x_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4878_, v_x_4879_, v_x_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_x_4880_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_00_u03c3_4887_, lean_object* v_e_4888_, lean_object* v_n_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4887_, v_e_4888_, v_n_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4905_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_4905_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4905_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
uint8_t v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4900_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4896_);
lean_dec(v_a_4896_);
v___x_4901_ = lean_box(v___x_4900_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_4901_);
v___x_4903_ = v___x_4898_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4895_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4895_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_00_u03c3_4914_, lean_object* v_e_4915_, lean_object* v_n_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_00_u03c3_4914_, v_e_4915_, v_n_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_n_4916_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
switch(lean_obj_tag(v_x_4923_))
{
case 1:
{
lean_object* v_fvarId_4929_; lean_object* v___x_4930_; 
v_fvarId_4929_ = lean_ctor_get(v_x_4923_, 0);
lean_inc(v_fvarId_4929_);
lean_dec_ref_known(v_x_4923_, 1);
v___x_4930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4929_, v_a_4924_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4933_ = lean_unsigned_to_nat(0u);
v___x_4934_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4932_, v_a_4931_, v___x_4933_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_4934_;
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
v_a_4935_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4930_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4930_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4943_; lean_object* v___x_4944_; 
v_mvarId_4943_ = lean_ctor_get(v_x_4923_, 0);
lean_inc(v_mvarId_4943_);
lean_dec_ref_known(v_x_4923_, 1);
v___x_4944_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4943_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___x_4944_, 1);
v___x_4946_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4946_, v_a_4945_, v___x_4947_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_4948_;
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4949_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4944_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4944_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
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
case 3:
{
uint8_t v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
lean_dec_ref_known(v_x_4923_, 1);
v___x_4957_ = 0;
v___x_4958_ = lean_box(v___x_4957_);
v___x_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4958_);
return v___x_4959_;
}
case 4:
{
lean_object* v_declName_4960_; lean_object* v_us_4961_; lean_object* v___x_4962_; 
v_declName_4960_ = lean_ctor_get(v_x_4923_, 0);
lean_inc(v_declName_4960_);
v_us_4961_ = lean_ctor_get(v_x_4923_, 1);
lean_inc(v_us_4961_);
lean_dec_ref_known(v_x_4923_, 2);
v___x_4962_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4960_, v_us_4961_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v_fst_4964_; lean_object* v_snd_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v_fst_4964_ = lean_ctor_get(v_a_4963_, 0);
lean_inc(v_fst_4964_);
v_snd_4965_ = lean_ctor_get(v_a_4963_, 1);
lean_inc(v_snd_4965_);
lean_dec(v_a_4963_);
v___x_4966_ = lean_unsigned_to_nat(0u);
v___x_4967_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4965_, v_fst_4964_, v___x_4966_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_4967_;
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
v_a_4968_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4962_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4962_);
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
case 5:
{
lean_object* v_fn_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v_fn_4976_ = lean_ctor_get(v_x_4923_, 0);
lean_inc_ref(v_fn_4976_);
lean_dec_ref_known(v_x_4923_, 2);
v___x_4977_ = lean_unsigned_to_nat(1u);
v___x_4978_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4976_, v___x_4977_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_4978_;
}
case 6:
{
lean_object* v_body_4979_; 
v_body_4979_ = lean_ctor_get(v_x_4923_, 2);
lean_inc_ref(v_body_4979_);
lean_dec_ref_known(v_x_4923_, 3);
v_x_4923_ = v_body_4979_;
goto _start;
}
case 7:
{
uint8_t v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
lean_dec_ref_known(v_x_4923_, 3);
v___x_4981_ = 0;
v___x_4982_ = lean_box(v___x_4981_);
v___x_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
return v___x_4983_;
}
case 8:
{
lean_object* v_body_4984_; 
v_body_4984_ = lean_ctor_get(v_x_4923_, 3);
lean_inc_ref(v_body_4984_);
lean_dec_ref_known(v_x_4923_, 4);
v_x_4923_ = v_body_4984_;
goto _start;
}
case 9:
{
uint8_t v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
lean_dec_ref_known(v_x_4923_, 1);
v___x_4986_ = 0;
v___x_4987_ = lean_box(v___x_4986_);
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
return v___x_4988_;
}
case 10:
{
lean_object* v_expr_4989_; 
v_expr_4989_ = lean_ctor_get(v_x_4923_, 1);
lean_inc_ref(v_expr_4989_);
lean_dec_ref_known(v_x_4923_, 2);
v_x_4923_ = v_expr_4989_;
goto _start;
}
default: 
{
uint8_t v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec_ref(v_x_4923_);
v___x_4991_ = 2;
v___x_4992_ = lean_box(v___x_4991_);
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
return v___x_4993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4994_, lean_object* v_x_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
switch(lean_obj_tag(v_x_4994_))
{
case 4:
{
lean_object* v_declName_5001_; lean_object* v_us_5002_; lean_object* v___x_5003_; 
v_declName_5001_ = lean_ctor_get(v_x_4994_, 0);
lean_inc(v_declName_5001_);
v_us_5002_ = lean_ctor_get(v_x_4994_, 1);
lean_inc(v_us_5002_);
lean_dec_ref_known(v_x_4994_, 2);
v___x_5003_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5001_, v_us_5002_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v_fst_5005_; lean_object* v_snd_5006_; lean_object* v___x_5007_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v_fst_5005_ = lean_ctor_get(v_a_5004_, 0);
lean_inc(v_fst_5005_);
v_snd_5006_ = lean_ctor_get(v_a_5004_, 1);
lean_inc(v_snd_5006_);
lean_dec(v_a_5004_);
v___x_5007_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_5006_, v_fst_5005_, v_x_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_x_4995_);
return v___x_5007_;
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec(v_x_4995_);
v_a_5008_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_5003_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_5003_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
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
case 1:
{
lean_object* v_fvarId_5016_; lean_object* v___x_5017_; 
v_fvarId_5016_ = lean_ctor_get(v_x_4994_, 0);
lean_inc(v_fvarId_5016_);
lean_dec_ref_known(v_x_4994_, 1);
v___x_5017_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5016_, v_a_4996_, v_a_4998_, v_a_4999_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5017_, 1);
v___x_5019_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5020_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5019_, v_a_5018_, v_x_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_x_4995_);
return v___x_5020_;
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_x_4995_);
v_a_5021_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5017_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5017_);
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
case 2:
{
lean_object* v_mvarId_5029_; lean_object* v___x_5030_; 
v_mvarId_5029_ = lean_ctor_get(v_x_4994_, 0);
lean_inc(v_mvarId_5029_);
lean_dec_ref_known(v_x_4994_, 1);
v___x_5030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5029_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v___x_5032_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5032_, v_a_5031_, v_x_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_x_4995_);
return v___x_5033_;
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_x_4995_);
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
case 5:
{
lean_object* v_fn_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v_fn_5042_ = lean_ctor_get(v_x_4994_, 0);
lean_inc_ref(v_fn_5042_);
lean_dec_ref_known(v_x_4994_, 2);
v___x_5043_ = lean_unsigned_to_nat(1u);
v___x_5044_ = lean_nat_add(v_x_4995_, v___x_5043_);
lean_dec(v_x_4995_);
v_x_4994_ = v_fn_5042_;
v_x_4995_ = v___x_5044_;
goto _start;
}
case 10:
{
lean_object* v_expr_5046_; 
v_expr_5046_ = lean_ctor_get(v_x_4994_, 1);
lean_inc_ref(v_expr_5046_);
lean_dec_ref_known(v_x_4994_, 2);
v_x_4994_ = v_expr_5046_;
goto _start;
}
case 8:
{
lean_object* v_body_5048_; 
v_body_5048_ = lean_ctor_get(v_x_4994_, 3);
lean_inc_ref(v_body_5048_);
lean_dec_ref_known(v_x_4994_, 4);
v_x_4994_ = v_body_5048_;
goto _start;
}
case 6:
{
lean_object* v_body_5050_; lean_object* v_zero_5051_; uint8_t v_isZero_5052_; 
v_body_5050_ = lean_ctor_get(v_x_4994_, 2);
lean_inc_ref(v_body_5050_);
lean_dec_ref_known(v_x_4994_, 3);
v_zero_5051_ = lean_unsigned_to_nat(0u);
v_isZero_5052_ = lean_nat_dec_eq(v_x_4995_, v_zero_5051_);
if (v_isZero_5052_ == 1)
{
lean_object* v___x_5053_; 
lean_dec(v_x_4995_);
v___x_5053_ = l_Lean_Meta_isProofQuick(v_body_5050_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
return v___x_5053_;
}
else
{
lean_object* v_one_5054_; lean_object* v_n_5055_; 
v_one_5054_ = lean_unsigned_to_nat(1u);
v_n_5055_ = lean_nat_sub(v_x_4995_, v_one_5054_);
lean_dec(v_x_4995_);
v_x_4994_ = v_body_5050_;
v_x_4995_ = v_n_5055_;
goto _start;
}
}
default: 
{
uint8_t v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
lean_dec(v_x_4995_);
lean_dec_ref(v_x_4994_);
v___x_5057_ = 2;
v___x_5058_ = lean_box(v___x_5057_);
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
return v___x_5059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_5060_, lean_object* v_x_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_5060_, v_x_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lean_Meta_isProofQuick(v_x_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v___x_5081_; 
lean_inc_ref(v_e_5075_);
v___x_5081_ = l_Lean_Meta_isProofQuick(v_e_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5108_; 
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5084_ = v___x_5081_;
v_isShared_5085_ = v_isSharedCheck_5108_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5081_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5108_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
uint8_t v___x_5086_; 
v___x_5086_ = lean_unbox(v_a_5082_);
lean_dec(v_a_5082_);
switch(v___x_5086_)
{
case 0:
{
uint8_t v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5090_; 
lean_dec_ref(v_e_5075_);
v___x_5087_ = 0;
v___x_5088_ = lean_box(v___x_5087_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 0, v___x_5088_);
v___x_5090_ = v___x_5084_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
case 1:
{
uint8_t v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5095_; 
lean_dec_ref(v_e_5075_);
v___x_5092_ = 1;
v___x_5093_ = lean_box(v___x_5092_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 0, v___x_5093_);
v___x_5095_ = v___x_5084_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
default: 
{
lean_object* v___x_5097_; 
lean_del_object(v___x_5084_);
lean_inc(v_a_5079_);
lean_inc_ref(v_a_5078_);
lean_inc(v_a_5077_);
lean_inc_ref(v_a_5076_);
v___x_5097_ = lean_infer_type(v_e_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v___x_5099_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
v___x_5099_ = l_Lean_Meta_isProp(v_a_5098_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_);
return v___x_5099_;
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
v_a_5100_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5097_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5097_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
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
}
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v_e_5075_);
v_a_5109_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5081_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5081_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_Meta_isProof(v_e_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_5124_, lean_object* v_x_5125_){
_start:
{
switch(lean_obj_tag(v_x_5124_))
{
case 3:
{
lean_object* v___x_5131_; uint8_t v___x_5132_; 
v___x_5131_ = lean_unsigned_to_nat(0u);
v___x_5132_ = lean_nat_dec_eq(v_x_5125_, v___x_5131_);
lean_dec(v_x_5125_);
if (v___x_5132_ == 0)
{
goto v___jp_5127_;
}
else
{
uint8_t v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5133_ = 1;
v___x_5134_ = lean_box(v___x_5133_);
v___x_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5134_);
return v___x_5135_;
}
}
case 7:
{
lean_object* v_body_5136_; lean_object* v_zero_5137_; uint8_t v_isZero_5138_; 
v_body_5136_ = lean_ctor_get(v_x_5124_, 2);
v_zero_5137_ = lean_unsigned_to_nat(0u);
v_isZero_5138_ = lean_nat_dec_eq(v_x_5125_, v_zero_5137_);
if (v_isZero_5138_ == 1)
{
uint8_t v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_dec(v_x_5125_);
v___x_5139_ = 0;
v___x_5140_ = lean_box(v___x_5139_);
v___x_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
return v___x_5141_;
}
else
{
lean_object* v_one_5142_; lean_object* v_n_5143_; 
v_one_5142_ = lean_unsigned_to_nat(1u);
v_n_5143_ = lean_nat_sub(v_x_5125_, v_one_5142_);
lean_dec(v_x_5125_);
v_x_5124_ = v_body_5136_;
v_x_5125_ = v_n_5143_;
goto _start;
}
}
case 8:
{
lean_object* v_body_5145_; 
v_body_5145_ = lean_ctor_get(v_x_5124_, 3);
v_x_5124_ = v_body_5145_;
goto _start;
}
case 10:
{
lean_object* v_expr_5147_; 
v_expr_5147_ = lean_ctor_get(v_x_5124_, 1);
v_x_5124_ = v_expr_5147_;
goto _start;
}
default: 
{
lean_dec(v_x_5125_);
goto v___jp_5127_;
}
}
v___jp_5127_:
{
uint8_t v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5128_ = 2;
v___x_5129_ = lean_box(v___x_5128_);
v___x_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5129_);
return v___x_5130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_5149_, lean_object* v_x_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5149_, v_x_5150_);
lean_dec_ref(v_x_5149_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_5153_, lean_object* v_x_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5153_, v_x_5154_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_5161_, lean_object* v_x_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_5161_, v_x_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v_x_5161_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_5169_, lean_object* v_x_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
switch(lean_obj_tag(v_x_5169_))
{
case 4:
{
lean_object* v_declName_5176_; lean_object* v_us_5177_; lean_object* v___x_5178_; 
v_declName_5176_ = lean_ctor_get(v_x_5169_, 0);
lean_inc(v_declName_5176_);
v_us_5177_ = lean_ctor_get(v_x_5169_, 1);
lean_inc(v_us_5177_);
lean_dec_ref_known(v_x_5169_, 2);
v___x_5178_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5176_, v_us_5177_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v_a_5179_; lean_object* v_fst_5180_; lean_object* v___x_5181_; 
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc(v_a_5179_);
lean_dec_ref_known(v___x_5178_, 1);
v_fst_5180_ = lean_ctor_get(v_a_5179_, 0);
lean_inc(v_fst_5180_);
lean_dec(v_a_5179_);
v___x_5181_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5180_, v_x_5170_);
lean_dec(v_fst_5180_);
return v___x_5181_;
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v_x_5170_);
v_a_5182_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5178_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5178_);
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
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
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
}
case 1:
{
lean_object* v_fvarId_5190_; lean_object* v___x_5191_; 
v_fvarId_5190_ = lean_ctor_get(v_x_5169_, 0);
lean_inc(v_fvarId_5190_);
lean_dec_ref_known(v_x_5169_, 1);
v___x_5191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5190_, v_a_5171_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v___x_5193_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
lean_inc(v_a_5192_);
lean_dec_ref_known(v___x_5191_, 1);
v___x_5193_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5192_, v_x_5170_);
lean_dec(v_a_5192_);
return v___x_5193_;
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec(v_x_5170_);
v_a_5194_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5191_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5191_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5202_; lean_object* v___x_5203_; 
v_mvarId_5202_ = lean_ctor_get(v_x_5169_, 0);
lean_inc(v_mvarId_5202_);
lean_dec_ref_known(v_x_5169_, 1);
v___x_5203_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5202_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5205_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5203_, 1);
v___x_5205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5204_, v_x_5170_);
lean_dec(v_a_5204_);
return v___x_5205_;
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
lean_dec(v_x_5170_);
v_a_5206_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5203_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5203_);
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
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
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
}
case 5:
{
lean_object* v_fn_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v_fn_5214_ = lean_ctor_get(v_x_5169_, 0);
lean_inc_ref(v_fn_5214_);
lean_dec_ref_known(v_x_5169_, 2);
v___x_5215_ = lean_unsigned_to_nat(1u);
v___x_5216_ = lean_nat_add(v_x_5170_, v___x_5215_);
lean_dec(v_x_5170_);
v_x_5169_ = v_fn_5214_;
v_x_5170_ = v___x_5216_;
goto _start;
}
case 10:
{
lean_object* v_expr_5218_; 
v_expr_5218_ = lean_ctor_get(v_x_5169_, 1);
lean_inc_ref(v_expr_5218_);
lean_dec_ref_known(v_x_5169_, 2);
v_x_5169_ = v_expr_5218_;
goto _start;
}
case 8:
{
lean_object* v_body_5220_; 
v_body_5220_ = lean_ctor_get(v_x_5169_, 3);
lean_inc_ref(v_body_5220_);
lean_dec_ref_known(v_x_5169_, 4);
v_x_5169_ = v_body_5220_;
goto _start;
}
case 6:
{
lean_object* v_body_5222_; lean_object* v_zero_5223_; uint8_t v_isZero_5224_; 
v_body_5222_ = lean_ctor_get(v_x_5169_, 2);
lean_inc_ref(v_body_5222_);
lean_dec_ref_known(v_x_5169_, 3);
v_zero_5223_ = lean_unsigned_to_nat(0u);
v_isZero_5224_ = lean_nat_dec_eq(v_x_5170_, v_zero_5223_);
if (v_isZero_5224_ == 1)
{
uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
lean_dec_ref(v_body_5222_);
lean_dec(v_x_5170_);
v___x_5225_ = 0;
v___x_5226_ = lean_box(v___x_5225_);
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
return v___x_5227_;
}
else
{
lean_object* v_one_5228_; lean_object* v_n_5229_; 
v_one_5228_ = lean_unsigned_to_nat(1u);
v_n_5229_ = lean_nat_sub(v_x_5170_, v_one_5228_);
lean_dec(v_x_5170_);
v_x_5169_ = v_body_5222_;
v_x_5170_ = v_n_5229_;
goto _start;
}
}
default: 
{
uint8_t v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
lean_dec(v_x_5170_);
lean_dec_ref(v_x_5169_);
v___x_5231_ = 2;
v___x_5232_ = lean_box(v___x_5231_);
v___x_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
return v___x_5233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_5234_, lean_object* v_x_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_5234_, v_x_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_);
lean_dec(v_a_5239_);
lean_dec_ref(v_a_5238_);
lean_dec(v_a_5237_);
lean_dec_ref(v_a_5236_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_){
_start:
{
switch(lean_obj_tag(v_x_5242_))
{
case 1:
{
lean_object* v_fvarId_5248_; lean_object* v___x_5249_; 
v_fvarId_5248_ = lean_ctor_get(v_x_5242_, 0);
lean_inc(v_fvarId_5248_);
lean_dec_ref_known(v_x_5242_, 1);
v___x_5249_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5248_, v_a_5243_, v_a_5245_, v_a_5246_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
lean_inc(v_a_5250_);
lean_dec_ref_known(v___x_5249_, 1);
v___x_5251_ = lean_unsigned_to_nat(0u);
v___x_5252_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5250_, v___x_5251_);
lean_dec(v_a_5250_);
return v___x_5252_;
}
else
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5260_; 
v_a_5253_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5255_ = v___x_5249_;
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5249_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5258_; 
if (v_isShared_5256_ == 0)
{
v___x_5258_ = v___x_5255_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5253_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5261_; lean_object* v___x_5262_; 
v_mvarId_5261_ = lean_ctor_get(v_x_5242_, 0);
lean_inc(v_mvarId_5261_);
lean_dec_ref_known(v_x_5242_, 1);
v___x_5262_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5261_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
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
case 3:
{
uint8_t v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
lean_dec_ref_known(v_x_5242_, 1);
v___x_5274_ = 1;
v___x_5275_ = lean_box(v___x_5274_);
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5275_);
return v___x_5276_;
}
case 4:
{
lean_object* v_declName_5277_; lean_object* v_us_5278_; lean_object* v___x_5279_; 
v_declName_5277_ = lean_ctor_get(v_x_5242_, 0);
lean_inc(v_declName_5277_);
v_us_5278_ = lean_ctor_get(v_x_5242_, 1);
lean_inc(v_us_5278_);
lean_dec_ref_known(v_x_5242_, 2);
v___x_5279_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5277_, v_us_5278_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v_fst_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
v_fst_5281_ = lean_ctor_get(v_a_5280_, 0);
lean_inc(v_fst_5281_);
lean_dec(v_a_5280_);
v___x_5282_ = lean_unsigned_to_nat(0u);
v___x_5283_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5281_, v___x_5282_);
lean_dec(v_fst_5281_);
return v___x_5283_;
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
v_a_5284_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5279_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5279_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
case 5:
{
lean_object* v_fn_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v_fn_5292_ = lean_ctor_get(v_x_5242_, 0);
lean_inc_ref(v_fn_5292_);
lean_dec_ref_known(v_x_5242_, 2);
v___x_5293_ = lean_unsigned_to_nat(1u);
v___x_5294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_5292_, v___x_5293_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_);
return v___x_5294_;
}
case 6:
{
uint8_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec_ref_known(v_x_5242_, 3);
v___x_5295_ = 0;
v___x_5296_ = lean_box(v___x_5295_);
v___x_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5296_);
return v___x_5297_;
}
case 7:
{
uint8_t v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
lean_dec_ref_known(v_x_5242_, 3);
v___x_5298_ = 1;
v___x_5299_ = lean_box(v___x_5298_);
v___x_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5300_, 0, v___x_5299_);
return v___x_5300_;
}
case 8:
{
lean_object* v_body_5301_; 
v_body_5301_ = lean_ctor_get(v_x_5242_, 3);
lean_inc_ref(v_body_5301_);
lean_dec_ref_known(v_x_5242_, 4);
v_x_5242_ = v_body_5301_;
goto _start;
}
case 9:
{
uint8_t v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; 
lean_dec_ref_known(v_x_5242_, 1);
v___x_5303_ = 0;
v___x_5304_ = lean_box(v___x_5303_);
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5304_);
return v___x_5305_;
}
case 10:
{
lean_object* v_expr_5306_; 
v_expr_5306_ = lean_ctor_get(v_x_5242_, 1);
lean_inc_ref(v_expr_5306_);
lean_dec_ref_known(v_x_5242_, 2);
v_x_5242_ = v_expr_5306_;
goto _start;
}
default: 
{
uint8_t v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_dec_ref(v_x_5242_);
v___x_5308_ = 2;
v___x_5309_ = lean_box(v___x_5308_);
v___x_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5309_);
return v___x_5310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_){
_start:
{
lean_object* v_res_5317_; 
v_res_5317_ = l_Lean_Meta_isTypeQuick(v_x_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_);
lean_dec(v_a_5315_);
lean_dec_ref(v_a_5314_);
lean_dec(v_a_5313_);
lean_dec_ref(v_a_5312_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
lean_object* v___x_5324_; 
lean_inc_ref(v_e_5318_);
v___x_5324_ = l_Lean_Meta_isTypeQuick(v_e_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5374_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5327_ = v___x_5324_;
v_isShared_5328_ = v_isSharedCheck_5374_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5324_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5374_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
uint8_t v___x_5329_; 
v___x_5329_ = lean_unbox(v_a_5325_);
lean_dec(v_a_5325_);
switch(v___x_5329_)
{
case 0:
{
uint8_t v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; 
lean_dec_ref(v_e_5318_);
v___x_5330_ = 0;
v___x_5331_ = lean_box(v___x_5330_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 0, v___x_5331_);
v___x_5333_ = v___x_5327_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
case 1:
{
uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5338_; 
lean_dec_ref(v_e_5318_);
v___x_5335_ = 1;
v___x_5336_ = lean_box(v___x_5335_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 0, v___x_5336_);
v___x_5338_ = v___x_5327_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5336_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
default: 
{
lean_object* v___x_5340_; 
lean_del_object(v___x_5327_);
lean_inc(v_a_5322_);
lean_inc_ref(v_a_5321_);
lean_inc(v_a_5320_);
lean_inc_ref(v_a_5319_);
v___x_5340_ = lean_infer_type(v_e_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; lean_object* v___x_5342_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref_known(v___x_5340_, 1);
v___x_5342_ = l_Lean_Meta_whnfD(v_a_5341_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5357_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5345_ = v___x_5342_;
v_isShared_5346_ = v_isSharedCheck_5357_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5342_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5357_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
if (lean_obj_tag(v_a_5343_) == 3)
{
uint8_t v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5350_; 
lean_dec_ref_known(v_a_5343_, 1);
v___x_5347_ = 1;
v___x_5348_ = lean_box(v___x_5347_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5348_);
v___x_5350_ = v___x_5345_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
else
{
uint8_t v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5355_; 
lean_dec(v_a_5343_);
v___x_5352_ = 0;
v___x_5353_ = lean_box(v___x_5352_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5353_);
v___x_5355_ = v___x_5345_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
v_a_5358_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5342_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5342_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
else
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
v_a_5366_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5340_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5340_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
lean_dec_ref(v_e_5318_);
v_a_5375_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5377_ = v___x_5324_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5324_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_){
_start:
{
lean_object* v_res_5389_; 
v_res_5389_ = l_Lean_Meta_isType(v_e_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_);
lean_dec(v_a_5387_);
lean_dec_ref(v_a_5386_);
lean_dec(v_a_5385_);
lean_dec_ref(v_a_5384_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_5390_){
_start:
{
switch(lean_obj_tag(v_x_5390_))
{
case 7:
{
lean_object* v_body_5391_; 
v_body_5391_ = lean_ctor_get(v_x_5390_, 2);
v_x_5390_ = v_body_5391_;
goto _start;
}
case 3:
{
lean_object* v_u_5393_; lean_object* v___x_5394_; 
v_u_5393_ = lean_ctor_get(v_x_5390_, 0);
lean_inc(v_u_5393_);
v___x_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_u_5393_);
return v___x_5394_;
}
default: 
{
lean_object* v___x_5395_; 
v___x_5395_ = lean_box(0);
return v___x_5395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_5396_);
lean_dec_ref(v_x_5396_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5398_, lean_object* v_body_5399_, lean_object* v_x_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5398_, v_body_5399_, v_x_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5409_, lean_object* v_xs_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_l_5417_; 
switch(lean_obj_tag(v_type_5409_))
{
case 3:
{
lean_object* v_u_5420_; 
lean_dec_ref(v_xs_5410_);
v_u_5420_ = lean_ctor_get(v_type_5409_, 0);
lean_inc(v_u_5420_);
lean_dec_ref_known(v_type_5409_, 1);
v_l_5417_ = v_u_5420_;
goto v___jp_5416_;
}
case 7:
{
lean_object* v_binderName_5421_; lean_object* v_binderType_5422_; lean_object* v_body_5423_; uint8_t v_binderInfo_5424_; lean_object* v___f_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; 
v_binderName_5421_ = lean_ctor_get(v_type_5409_, 0);
lean_inc(v_binderName_5421_);
v_binderType_5422_ = lean_ctor_get(v_type_5409_, 1);
lean_inc_ref(v_binderType_5422_);
v_body_5423_ = lean_ctor_get(v_type_5409_, 2);
lean_inc_ref(v_body_5423_);
v_binderInfo_5424_ = lean_ctor_get_uint8(v_type_5409_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5409_, 3);
lean_inc_ref(v_xs_5410_);
v___f_5425_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5425_, 0, v_xs_5410_);
lean_closure_set(v___f_5425_, 1, v_body_5423_);
v___x_5426_ = lean_expr_instantiate_rev(v_binderType_5422_, v_xs_5410_);
lean_dec_ref(v_xs_5410_);
lean_dec_ref(v_binderType_5422_);
v___x_5427_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5421_, v_binderInfo_5424_, v___x_5426_, v___f_5425_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_);
return v___x_5427_;
}
default: 
{
lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5428_ = lean_expr_instantiate_rev(v_type_5409_, v_xs_5410_);
lean_dec_ref(v_xs_5410_);
lean_dec_ref(v_type_5409_);
v___x_5429_ = l_Lean_Meta_whnfD(v___x_5428_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5441_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5441_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5441_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
switch(lean_obj_tag(v_a_5430_))
{
case 3:
{
lean_object* v_u_5434_; 
lean_del_object(v___x_5432_);
v_u_5434_ = lean_ctor_get(v_a_5430_, 0);
lean_inc(v_u_5434_);
lean_dec_ref_known(v_a_5430_, 1);
v_l_5417_ = v_u_5434_;
goto v___jp_5416_;
}
case 7:
{
lean_object* v___x_5435_; 
lean_del_object(v___x_5432_);
v___x_5435_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5409_ = v_a_5430_;
v_xs_5410_ = v___x_5435_;
goto _start;
}
default: 
{
lean_object* v___x_5437_; lean_object* v___x_5439_; 
lean_dec(v_a_5430_);
v___x_5437_ = lean_box(0);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5437_);
v___x_5439_ = v___x_5432_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
v_a_5442_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5429_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5429_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
}
v___jp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5418_, 0, v_l_5417_);
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
return v___x_5419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5450_, lean_object* v_body_5451_, lean_object* v_x_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = lean_array_push(v_xs_5450_, v_x_5452_);
v___x_5459_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5451_, v___x_5458_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5460_, lean_object* v_xs_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5460_, v_xs_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5468_, lean_object* v_cache_5469_, lean_object* v_a_x3f_5470_){
_start:
{
lean_object* v___x_5472_; lean_object* v_mctx_5473_; lean_object* v_zetaDeltaFVarIds_5474_; lean_object* v_postponed_5475_; lean_object* v_diag_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5486_; 
v___x_5472_ = lean_st_ref_take(v_a_5468_);
v_mctx_5473_ = lean_ctor_get(v___x_5472_, 0);
v_zetaDeltaFVarIds_5474_ = lean_ctor_get(v___x_5472_, 2);
v_postponed_5475_ = lean_ctor_get(v___x_5472_, 3);
v_diag_5476_ = lean_ctor_get(v___x_5472_, 4);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5486_ == 0)
{
lean_object* v_unused_5487_; 
v_unused_5487_ = lean_ctor_get(v___x_5472_, 1);
lean_dec(v_unused_5487_);
v___x_5478_ = v___x_5472_;
v_isShared_5479_ = v_isSharedCheck_5486_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_diag_5476_);
lean_inc(v_postponed_5475_);
lean_inc(v_zetaDeltaFVarIds_5474_);
lean_inc(v_mctx_5473_);
lean_dec(v___x_5472_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5486_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5480_; lean_object* v___x_5482_; 
v___x_5480_ = lean_box(0);
if (v_isShared_5479_ == 0)
{
lean_ctor_set(v___x_5478_, 1, v_cache_5469_);
v___x_5482_ = v___x_5478_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_mctx_5473_);
lean_ctor_set(v_reuseFailAlloc_5485_, 1, v_cache_5469_);
lean_ctor_set(v_reuseFailAlloc_5485_, 2, v_zetaDeltaFVarIds_5474_);
lean_ctor_set(v_reuseFailAlloc_5485_, 3, v_postponed_5475_);
lean_ctor_set(v_reuseFailAlloc_5485_, 4, v_diag_5476_);
v___x_5482_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = lean_st_ref_put(v_a_5468_, v___x_5482_);
v___x_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5480_);
return v___x_5484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5488_, lean_object* v_cache_5489_, lean_object* v_a_x3f_5490_, lean_object* v___y_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5488_, v_cache_5489_, v_a_x3f_5490_);
lean_dec(v_a_x3f_5490_);
lean_dec(v_a_5488_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5493_);
if (lean_obj_tag(v___x_5499_) == 0)
{
lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v_cache_5502_; lean_object* v___x_5503_; 
v___x_5500_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5501_ = lean_st_ref_get(v_a_5495_);
v_cache_5502_ = lean_ctor_get(v___x_5501_, 1);
lean_inc_ref(v_cache_5502_);
lean_dec(v___x_5501_);
v___x_5503_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5493_, v___x_5500_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5520_; 
v_a_5504_ = lean_ctor_get(v___x_5503_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5506_ = v___x_5503_;
v_isShared_5507_ = v_isSharedCheck_5520_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5503_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5520_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
lean_inc(v_a_5504_);
if (v_isShared_5507_ == 0)
{
lean_ctor_set_tag(v___x_5506_, 1);
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
v___x_5510_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5495_, v_cache_5502_, v___x_5509_);
lean_dec_ref(v___x_5509_);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5517_ == 0)
{
lean_object* v_unused_5518_; 
v_unused_5518_ = lean_ctor_get(v___x_5510_, 0);
lean_dec(v_unused_5518_);
v___x_5512_ = v___x_5510_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_dec(v___x_5510_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 0, v_a_5504_);
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5504_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v_a_5521_ = lean_ctor_get(v___x_5503_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v___x_5503_, 1);
v___x_5522_ = lean_box(0);
v___x_5523_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5495_, v_cache_5502_, v___x_5522_);
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
lean_ctor_set_tag(v___x_5525_, 1);
lean_ctor_set(v___x_5525_, 0, v_a_5521_);
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5521_);
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
else
{
lean_object* v___x_5532_; 
lean_dec_ref(v_type_5493_);
v___x_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5499_);
return v___x_5532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_);
lean_dec(v_a_5537_);
lean_dec_ref(v_a_5536_);
lean_dec(v_a_5535_);
lean_dec_ref(v_a_5534_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_){
_start:
{
lean_object* v___x_5546_; 
v___x_5546_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5561_; 
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5549_ = v___x_5546_;
v_isShared_5550_ = v_isSharedCheck_5561_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5546_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5561_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
if (lean_obj_tag(v_a_5547_) == 0)
{
uint8_t v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5554_; 
v___x_5551_ = 0;
v___x_5552_ = lean_box(v___x_5551_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 0, v___x_5552_);
v___x_5554_ = v___x_5549_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
else
{
uint8_t v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5559_; 
lean_dec_ref_known(v_a_5547_, 1);
v___x_5556_ = 1;
v___x_5557_ = lean_box(v___x_5556_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 0, v___x_5557_);
v___x_5559_ = v___x_5549_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
v_a_5562_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5546_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5546_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_){
_start:
{
lean_object* v_res_5576_; 
v_res_5576_ = l_Lean_Meta_isTypeFormerType(v_type_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_);
lean_dec(v_a_5574_);
lean_dec_ref(v_a_5573_);
lean_dec(v_a_5572_);
lean_dec_ref(v_a_5571_);
return v_res_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v___x_5583_; 
v___x_5583_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5599_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5586_ = v___x_5583_;
v_isShared_5587_ = v_isSharedCheck_5599_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5583_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5599_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
if (lean_obj_tag(v_a_5584_) == 1)
{
lean_object* v_val_5588_; uint8_t v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5592_; 
v_val_5588_ = lean_ctor_get(v_a_5584_, 0);
lean_inc(v_val_5588_);
lean_dec_ref_known(v_a_5584_, 1);
v___x_5589_ = l_Lean_Level_isAlwaysZero(v_val_5588_);
lean_dec(v_val_5588_);
v___x_5590_ = lean_box(v___x_5589_);
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v___x_5590_);
v___x_5592_ = v___x_5586_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5590_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
else
{
uint8_t v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5597_; 
lean_dec(v_a_5584_);
v___x_5594_ = 0;
v___x_5595_ = lean_box(v___x_5594_);
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v___x_5595_);
v___x_5597_ = v___x_5586_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v___x_5595_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
v_a_5600_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5583_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5583_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Lean_Meta_isPropFormerType(v_type_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_);
lean_dec(v_a_5612_);
lean_dec_ref(v_a_5611_);
lean_dec(v_a_5610_);
lean_dec_ref(v_a_5609_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_){
_start:
{
lean_object* v___x_5621_; 
lean_inc(v_a_5619_);
lean_inc_ref(v_a_5618_);
lean_inc(v_a_5617_);
lean_inc_ref(v_a_5616_);
v___x_5621_ = lean_infer_type(v_e_5615_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5622_; lean_object* v___x_5623_; 
v_a_5622_ = lean_ctor_get(v___x_5621_, 0);
lean_inc(v_a_5622_);
lean_dec_ref_known(v___x_5621_, 1);
v___x_5623_ = l_Lean_Meta_isTypeFormerType(v_a_5622_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_);
return v___x_5623_;
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
v_a_5624_ = lean_ctor_get(v___x_5621_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5621_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5621_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l_Lean_Meta_isTypeFormer(v_e_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5639_, lean_object* v_maxFVars_x3f_5640_, lean_object* v_k_5641_, uint8_t v_cleanupAnnotations_5642_, uint8_t v_whnfType_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v___f_5649_; lean_object* v___x_5650_; 
v___f_5649_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5649_, 0, v_k_5641_);
v___x_5650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5639_, v_maxFVars_x3f_5640_, v___f_5649_, v_cleanupAnnotations_5642_, v_whnfType_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5650_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5650_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
v_a_5659_ = lean_ctor_get(v___x_5650_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5650_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5650_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5667_, lean_object* v_maxFVars_x3f_5668_, lean_object* v_k_5669_, lean_object* v_cleanupAnnotations_5670_, lean_object* v_whnfType_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5677_; uint8_t v_whnfType_boxed_5678_; lean_object* v_res_5679_; 
v_cleanupAnnotations_boxed_5677_ = lean_unbox(v_cleanupAnnotations_5670_);
v_whnfType_boxed_5678_ = lean_unbox(v_whnfType_5671_);
v_res_5679_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5667_, v_maxFVars_x3f_5668_, v_k_5669_, v_cleanupAnnotations_boxed_5677_, v_whnfType_boxed_5678_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5680_, lean_object* v_type_5681_, lean_object* v_maxFVars_x3f_5682_, lean_object* v_k_5683_, uint8_t v_cleanupAnnotations_5684_, uint8_t v_whnfType_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_){
_start:
{
lean_object* v___x_5691_; 
v___x_5691_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5681_, v_maxFVars_x3f_5682_, v_k_5683_, v_cleanupAnnotations_5684_, v_whnfType_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5692_, lean_object* v_type_5693_, lean_object* v_maxFVars_x3f_5694_, lean_object* v_k_5695_, lean_object* v_cleanupAnnotations_5696_, lean_object* v_whnfType_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5703_; uint8_t v_whnfType_boxed_5704_; lean_object* v_res_5705_; 
v_cleanupAnnotations_boxed_5703_ = lean_unbox(v_cleanupAnnotations_5696_);
v_whnfType_boxed_5704_ = lean_unbox(v_whnfType_5697_);
v_res_5705_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5692_, v_type_5693_, v_maxFVars_x3f_5694_, v_k_5695_, v_cleanupAnnotations_boxed_5703_, v_whnfType_boxed_5704_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
return v_res_5705_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5706_, lean_object* v_as_5707_, size_t v_i_5708_, size_t v_stop_5709_){
_start:
{
uint8_t v___x_5710_; 
v___x_5710_ = lean_usize_dec_eq(v_i_5708_, v_stop_5709_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; uint8_t v___x_5712_; 
v___x_5711_ = lean_array_uget_borrowed(v_as_5707_, v_i_5708_);
v___x_5712_ = lean_expr_eqv(v_a_5706_, v___x_5711_);
if (v___x_5712_ == 0)
{
size_t v___x_5713_; size_t v___x_5714_; 
v___x_5713_ = ((size_t)1ULL);
v___x_5714_ = lean_usize_add(v_i_5708_, v___x_5713_);
v_i_5708_ = v___x_5714_;
goto _start;
}
else
{
return v___x_5712_;
}
}
else
{
uint8_t v___x_5716_; 
v___x_5716_ = 0;
return v___x_5716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5717_, lean_object* v_as_5718_, lean_object* v_i_5719_, lean_object* v_stop_5720_){
_start:
{
size_t v_i_boxed_5721_; size_t v_stop_boxed_5722_; uint8_t v_res_5723_; lean_object* v_r_5724_; 
v_i_boxed_5721_ = lean_unbox_usize(v_i_5719_);
lean_dec(v_i_5719_);
v_stop_boxed_5722_ = lean_unbox_usize(v_stop_5720_);
lean_dec(v_stop_5720_);
v_res_5723_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5717_, v_as_5718_, v_i_boxed_5721_, v_stop_boxed_5722_);
lean_dec_ref(v_as_5718_);
lean_dec_ref(v_a_5717_);
v_r_5724_ = lean_box(v_res_5723_);
return v_r_5724_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5725_, lean_object* v_a_5726_){
_start:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v___x_5727_ = lean_unsigned_to_nat(0u);
v___x_5728_ = lean_array_get_size(v_as_5725_);
v___x_5729_ = lean_nat_dec_lt(v___x_5727_, v___x_5728_);
if (v___x_5729_ == 0)
{
return v___x_5729_;
}
else
{
size_t v___x_5730_; size_t v___x_5731_; uint8_t v___x_5732_; 
v___x_5730_ = ((size_t)0ULL);
v___x_5731_ = lean_usize_of_nat(v___x_5728_);
v___x_5732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5726_, v_as_5725_, v___x_5730_, v___x_5731_);
return v___x_5732_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5733_, lean_object* v_a_5734_){
_start:
{
uint8_t v_res_5735_; lean_object* v_r_5736_; 
v_res_5735_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5733_, v_a_5734_);
lean_dec_ref(v_a_5734_);
lean_dec_ref(v_as_5733_);
v_r_5736_ = lean_box(v_res_5735_);
return v_r_5736_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5737_, lean_object* v_e_5738_){
_start:
{
uint8_t v___x_5739_; lean_object* v_d_5741_; lean_object* v_b_5742_; 
v___x_5739_ = l_Lean_Expr_hasFVar(v_e_5738_);
if (v___x_5739_ == 0)
{
lean_dec_ref(v_e_5738_);
return v___x_5739_;
}
else
{
switch(lean_obj_tag(v_e_5738_))
{
case 7:
{
lean_object* v_binderType_5745_; lean_object* v_body_5746_; 
v_binderType_5745_ = lean_ctor_get(v_e_5738_, 1);
lean_inc_ref(v_binderType_5745_);
v_body_5746_ = lean_ctor_get(v_e_5738_, 2);
lean_inc_ref(v_body_5746_);
lean_dec_ref_known(v_e_5738_, 3);
v_d_5741_ = v_binderType_5745_;
v_b_5742_ = v_body_5746_;
goto v___jp_5740_;
}
case 6:
{
lean_object* v_binderType_5747_; lean_object* v_body_5748_; 
v_binderType_5747_ = lean_ctor_get(v_e_5738_, 1);
lean_inc_ref(v_binderType_5747_);
v_body_5748_ = lean_ctor_get(v_e_5738_, 2);
lean_inc_ref(v_body_5748_);
lean_dec_ref_known(v_e_5738_, 3);
v_d_5741_ = v_binderType_5747_;
v_b_5742_ = v_body_5748_;
goto v___jp_5740_;
}
case 10:
{
lean_object* v_expr_5749_; 
v_expr_5749_ = lean_ctor_get(v_e_5738_, 1);
lean_inc_ref(v_expr_5749_);
lean_dec_ref_known(v_e_5738_, 2);
v_e_5738_ = v_expr_5749_;
goto _start;
}
case 8:
{
lean_object* v_type_5751_; lean_object* v_value_5752_; lean_object* v_body_5753_; uint8_t v___x_5754_; 
v_type_5751_ = lean_ctor_get(v_e_5738_, 1);
lean_inc_ref(v_type_5751_);
v_value_5752_ = lean_ctor_get(v_e_5738_, 2);
lean_inc_ref(v_value_5752_);
v_body_5753_ = lean_ctor_get(v_e_5738_, 3);
lean_inc_ref(v_body_5753_);
lean_dec_ref_known(v_e_5738_, 4);
v___x_5754_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5737_, v_type_5751_);
if (v___x_5754_ == 0)
{
uint8_t v___x_5755_; 
v___x_5755_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5737_, v_value_5752_);
if (v___x_5755_ == 0)
{
v_e_5738_ = v_body_5753_;
goto _start;
}
else
{
lean_dec_ref(v_body_5753_);
return v___x_5739_;
}
}
else
{
lean_dec_ref(v_body_5753_);
lean_dec_ref(v_value_5752_);
return v___x_5739_;
}
}
case 5:
{
lean_object* v_fn_5757_; lean_object* v_arg_5758_; uint8_t v___x_5759_; 
v_fn_5757_ = lean_ctor_get(v_e_5738_, 0);
lean_inc_ref(v_fn_5757_);
v_arg_5758_ = lean_ctor_get(v_e_5738_, 1);
lean_inc_ref(v_arg_5758_);
lean_dec_ref_known(v_e_5738_, 2);
v___x_5759_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5737_, v_fn_5757_);
if (v___x_5759_ == 0)
{
v_e_5738_ = v_arg_5758_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5758_);
return v___x_5739_;
}
}
case 11:
{
lean_object* v_struct_5761_; 
v_struct_5761_ = lean_ctor_get(v_e_5738_, 2);
lean_inc_ref(v_struct_5761_);
lean_dec_ref_known(v_e_5738_, 3);
v_e_5738_ = v_struct_5761_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5763_; lean_object* v___x_5764_; uint8_t v___x_5765_; 
v_fvarId_5763_ = lean_ctor_get(v_e_5738_, 0);
lean_inc(v_fvarId_5763_);
lean_dec_ref_known(v_e_5738_, 1);
v___x_5764_ = l_Lean_Expr_fvar___override(v_fvarId_5763_);
v___x_5765_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5737_, v___x_5764_);
lean_dec_ref(v___x_5764_);
return v___x_5765_;
}
default: 
{
uint8_t v___x_5766_; 
lean_dec_ref(v_e_5738_);
v___x_5766_ = 0;
return v___x_5766_;
}
}
}
v___jp_5740_:
{
uint8_t v___x_5743_; 
v___x_5743_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5737_, v_d_5741_);
if (v___x_5743_ == 0)
{
v_e_5738_ = v_b_5742_;
goto _start;
}
else
{
lean_dec_ref(v_b_5742_);
return v___x_5739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5767_, lean_object* v_e_5768_){
_start:
{
uint8_t v_res_5769_; lean_object* v_r_5770_; 
v_res_5769_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5767_, v_e_5768_);
lean_dec_ref(v_xs_5767_);
v_r_5770_ = lean_box(v_res_5769_);
return v_r_5770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5772_; lean_object* v___x_5773_; 
v___x_5772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5773_ = l_Lean_stringToMessageData(v___x_5772_);
return v___x_5773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5775_; lean_object* v___x_5776_; 
v___x_5775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5776_ = l_Lean_stringToMessageData(v___x_5775_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5777_, lean_object* v_type_5778_, lean_object* v_as_5779_, size_t v_sz_5780_, size_t v_i_5781_, lean_object* v_b_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
lean_object* v_a_5789_; uint8_t v___x_5793_; 
v___x_5793_ = lean_usize_dec_lt(v_i_5781_, v_sz_5780_);
if (v___x_5793_ == 0)
{
lean_object* v___x_5794_; 
lean_dec_ref(v_type_5778_);
v___x_5794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5794_, 0, v_b_5782_);
return v___x_5794_;
}
else
{
lean_object* v___x_5795_; lean_object* v_a_5796_; uint8_t v___x_5797_; 
v___x_5795_ = lean_box(0);
v_a_5796_ = lean_array_uget_borrowed(v_as_5779_, v_i_5781_);
lean_inc(v_a_5796_);
v___x_5797_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5777_, v_a_5796_);
if (v___x_5797_ == 0)
{
v_a_5789_ = v___x_5795_;
goto v___jp_5788_;
}
else
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5796_);
v___x_5799_ = l_Lean_MessageData_ofExpr(v_a_5796_);
v___x_5800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5798_);
lean_ctor_set(v___x_5800_, 1, v___x_5799_);
v___x_5801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5802_, 0, v___x_5800_);
lean_ctor_set(v___x_5802_, 1, v___x_5801_);
lean_inc_ref(v_type_5778_);
v___x_5803_ = l_Lean_MessageData_ofExpr(v_type_5778_);
v___x_5804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5802_);
lean_ctor_set(v___x_5804_, 1, v___x_5803_);
v___x_5805_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5804_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
if (lean_obj_tag(v___x_5805_) == 0)
{
lean_dec_ref_known(v___x_5805_, 1);
v_a_5789_ = v___x_5795_;
goto v___jp_5788_;
}
else
{
lean_dec_ref(v_type_5778_);
return v___x_5805_;
}
}
}
v___jp_5788_:
{
size_t v___x_5790_; size_t v___x_5791_; 
v___x_5790_ = ((size_t)1ULL);
v___x_5791_ = lean_usize_add(v_i_5781_, v___x_5790_);
v_i_5781_ = v___x_5791_;
v_b_5782_ = v_a_5789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5806_, lean_object* v_type_5807_, lean_object* v_as_5808_, lean_object* v_sz_5809_, lean_object* v_i_5810_, lean_object* v_b_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
size_t v_sz_boxed_5817_; size_t v_i_boxed_5818_; lean_object* v_res_5819_; 
v_sz_boxed_5817_ = lean_unbox_usize(v_sz_5809_);
lean_dec(v_sz_5809_);
v_i_boxed_5818_ = lean_unbox_usize(v_i_5810_);
lean_dec(v_i_5810_);
v_res_5819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5806_, v_type_5807_, v_as_5808_, v_sz_boxed_5817_, v_i_boxed_5818_, v_b_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec(v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v___y_5813_);
lean_dec_ref(v___y_5812_);
lean_dec_ref(v_as_5808_);
lean_dec_ref(v_xs_5806_);
return v_res_5819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5820_, size_t v_i_5821_, lean_object* v_bs_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
uint8_t v___x_5828_; 
v___x_5828_ = lean_usize_dec_lt(v_i_5821_, v_sz_5820_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; 
v___x_5829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5829_, 0, v_bs_5822_);
return v___x_5829_;
}
else
{
lean_object* v_v_5830_; lean_object* v___x_5831_; lean_object* v_bs_x27_5832_; lean_object* v___x_5833_; 
v_v_5830_ = lean_array_uget(v_bs_5822_, v_i_5821_);
v___x_5831_ = lean_unsigned_to_nat(0u);
v_bs_x27_5832_ = lean_array_uset(v_bs_5822_, v_i_5821_, v___x_5831_);
lean_inc(v___y_5826_);
lean_inc_ref(v___y_5825_);
lean_inc(v___y_5824_);
lean_inc_ref(v___y_5823_);
v___x_5833_ = lean_infer_type(v_v_5830_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v_a_5834_; size_t v___x_5835_; size_t v___x_5836_; lean_object* v___x_5837_; 
v_a_5834_ = lean_ctor_get(v___x_5833_, 0);
lean_inc(v_a_5834_);
lean_dec_ref_known(v___x_5833_, 1);
v___x_5835_ = ((size_t)1ULL);
v___x_5836_ = lean_usize_add(v_i_5821_, v___x_5835_);
v___x_5837_ = lean_array_uset(v_bs_x27_5832_, v_i_5821_, v_a_5834_);
v_i_5821_ = v___x_5836_;
v_bs_5822_ = v___x_5837_;
goto _start;
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_dec_ref(v_bs_x27_5832_);
v_a_5839_ = lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5833_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5833_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5833_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5844_; 
if (v_isShared_5842_ == 0)
{
v___x_5844_ = v___x_5841_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5847_, lean_object* v_i_5848_, lean_object* v_bs_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
size_t v_sz_boxed_5855_; size_t v_i_boxed_5856_; lean_object* v_res_5857_; 
v_sz_boxed_5855_ = lean_unbox_usize(v_sz_5847_);
lean_dec(v_sz_5847_);
v_i_boxed_5856_ = lean_unbox_usize(v_i_5848_);
lean_dec(v_i_5848_);
v_res_5857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5855_, v_i_boxed_5856_, v_bs_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
return v_res_5857_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5860_ = l_Lean_stringToMessageData(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5863_ = l_Lean_stringToMessageData(v___x_5862_);
return v___x_5863_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5866_ = l_Lean_stringToMessageData(v___x_5865_);
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5867_, lean_object* v_n_5868_, lean_object* v_xs_5869_, lean_object* v_x_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_){
_start:
{
lean_object* v___x_5900_; uint8_t v___x_5901_; 
v___x_5900_ = lean_array_get_size(v_xs_5869_);
v___x_5901_ = lean_nat_dec_eq(v___x_5900_, v_n_5868_);
if (v___x_5901_ == 0)
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v_a_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5921_; 
lean_dec_ref(v_xs_5869_);
v___x_5902_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5903_ = l_Lean_MessageData_ofExpr(v_type_5867_);
v___x_5904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5902_);
lean_ctor_set(v___x_5904_, 1, v___x_5903_);
v___x_5905_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = l_Nat_reprFast(v_n_5868_);
v___x_5908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5907_);
v___x_5909_ = l_Lean_MessageData_ofFormat(v___x_5908_);
v___x_5910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5906_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5912_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
v_a_5914_ = lean_ctor_get(v___x_5913_, 0);
v_isSharedCheck_5921_ = !lean_is_exclusive(v___x_5913_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5916_ = v___x_5913_;
v_isShared_5917_ = v_isSharedCheck_5921_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_a_5914_);
lean_dec(v___x_5913_);
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
else
{
lean_dec(v_n_5868_);
goto v___jp_5876_;
}
v___jp_5876_:
{
size_t v_sz_5877_; size_t v___x_5878_; lean_object* v___x_5879_; 
v_sz_5877_ = lean_array_size(v_xs_5869_);
v___x_5878_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5869_);
v___x_5879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5877_, v___x_5878_, v_xs_5869_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
if (lean_obj_tag(v___x_5879_) == 0)
{
lean_object* v_a_5880_; lean_object* v___x_5881_; size_t v_sz_5882_; lean_object* v___x_5883_; 
v_a_5880_ = lean_ctor_get(v___x_5879_, 0);
lean_inc(v_a_5880_);
lean_dec_ref_known(v___x_5879_, 1);
v___x_5881_ = lean_box(0);
v_sz_5882_ = lean_array_size(v_a_5880_);
v___x_5883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5869_, v_type_5867_, v_a_5880_, v_sz_5882_, v___x_5878_, v___x_5881_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
lean_dec_ref(v_xs_5869_);
if (lean_obj_tag(v___x_5883_) == 0)
{
lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_5890_ == 0)
{
lean_object* v_unused_5891_; 
v_unused_5891_ = lean_ctor_get(v___x_5883_, 0);
lean_dec(v_unused_5891_);
v___x_5885_ = v___x_5883_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_dec(v___x_5883_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 0, v_a_5880_);
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5880_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
else
{
lean_object* v_a_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5899_; 
lean_dec(v_a_5880_);
v_a_5892_ = lean_ctor_get(v___x_5883_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5894_ = v___x_5883_;
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_a_5892_);
lean_dec(v___x_5883_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v___x_5897_; 
if (v_isShared_5895_ == 0)
{
v___x_5897_ = v___x_5894_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5869_);
lean_dec_ref(v_type_5867_);
return v___x_5879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5922_, lean_object* v_n_5923_, lean_object* v_xs_5924_, lean_object* v_x_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_){
_start:
{
lean_object* v_res_5931_; 
v_res_5931_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5922_, v_n_5923_, v_xs_5924_, v_x_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
lean_dec(v___y_5929_);
lean_dec_ref(v___y_5928_);
lean_dec(v___y_5927_);
lean_dec_ref(v___y_5926_);
lean_dec_ref(v_x_5925_);
return v_res_5931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5932_, lean_object* v_type_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_){
_start:
{
lean_object* v___f_5939_; lean_object* v___x_5940_; uint8_t v___x_5941_; lean_object* v___x_5942_; 
lean_inc(v_n_5932_);
lean_inc_ref(v_type_5933_);
v___f_5939_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5939_, 0, v_type_5933_);
lean_closure_set(v___f_5939_, 1, v_n_5932_);
v___x_5940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5940_, 0, v_n_5932_);
v___x_5941_ = 0;
v___x_5942_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5933_, v___x_5940_, v___f_5939_, v___x_5941_, v___x_5941_, v_a_5934_, v_a_5935_, v_a_5936_, v_a_5937_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5943_, lean_object* v_type_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_Lean_Meta_arrowDomainsN(v_n_5943_, v_type_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5951_, lean_object* v_e_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_){
_start:
{
lean_object* v___x_5958_; 
lean_inc(v_a_5956_);
lean_inc_ref(v_a_5955_);
lean_inc(v_a_5954_);
lean_inc_ref(v_a_5953_);
v___x_5958_ = lean_infer_type(v_e_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_);
if (lean_obj_tag(v___x_5958_) == 0)
{
lean_object* v_a_5959_; lean_object* v___x_5960_; 
v_a_5959_ = lean_ctor_get(v___x_5958_, 0);
lean_inc(v_a_5959_);
lean_dec_ref_known(v___x_5958_, 1);
v___x_5960_ = l_Lean_Meta_arrowDomainsN(v_n_5951_, v_a_5959_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_);
return v___x_5960_;
}
else
{
lean_object* v_a_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5968_; 
lean_dec(v_n_5951_);
v_a_5961_ = lean_ctor_get(v___x_5958_, 0);
v_isSharedCheck_5968_ = !lean_is_exclusive(v___x_5958_);
if (v_isSharedCheck_5968_ == 0)
{
v___x_5963_ = v___x_5958_;
v_isShared_5964_ = v_isSharedCheck_5968_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_a_5961_);
lean_dec(v___x_5958_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5968_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
lean_object* v___x_5966_; 
if (v_isShared_5964_ == 0)
{
v___x_5966_ = v___x_5963_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v_a_5961_);
v___x_5966_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
return v___x_5966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5969_, lean_object* v_e_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_){
_start:
{
lean_object* v_res_5976_; 
v_res_5976_ = l_Lean_Meta_inferArgumentTypesN(v_n_5969_, v_e_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_);
lean_dec(v_a_5974_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec_ref(v_a_5971_);
return v_res_5976_;
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
